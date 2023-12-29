use std::sync::atomic::{AtomicU32, Ordering};

static COUNTER: AtomicU32 = AtomicU32::new(0);

fn fresh() -> String {
    COUNTER.fetch_add(1, Ordering::SeqCst); // Automatically handles wrapping at 256!
    let c = COUNTER.load(Ordering::SeqCst) as u32;
    format!("v{c}")
}

pub type Id = String;

#[derive(Clone)]
pub enum Expr {
    Lam(Id, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Var(Id),
}

#[derive(PartialEq, Eq)]
pub enum DeBrujin {
    Lam(Box<DeBrujin>),
    App(Box<DeBrujin>, Box<DeBrujin>),
    Var(u32),
}

impl ToString for Expr {
    fn to_string(&self) -> String {
        match self {
            Expr::Lam(id, expr) => format!("(λ{}. {})", id, expr.to_string()),
            Expr::App(expr1, expr2) => format!("({} {})", expr1.to_string(), expr2.to_string()),
            Expr::Var(id) => id.clone(),
        }
    }
}

impl ToString for DeBrujin {
    fn to_string(&self) -> String {
        match self {
            DeBrujin::Lam(expr) => format!("(λ. {})", expr.to_string()),
            DeBrujin::App(expr1, expr2) => format!("({} {})", expr1.to_string(), expr2.to_string()),
            DeBrujin::Var(id) => format!("{}", id),
        }
    }
}

impl Expr {
    fn fv(&self) -> Vec<Id> {
        match self {
            Expr::Lam(id, expr) => {
                let mut fv = expr.fv();
                fv.retain(|x| x != id);
                fv
            }
            Expr::App(expr1, expr2) => {
                let mut fv1 = expr1.fv();
                let mut fv2 = expr2.fv();
                fv1.append(&mut fv2);
                fv1
            }
            Expr::Var(id) => vec![id.clone()],
        }
    }

    fn debrujin(&self) -> DeBrujin {
        self.debrujin_with(&vec![])
    }

    fn debrujin_with(&self, ctx: &Vec<Id>) -> DeBrujin {
        match self {
            Expr::Lam(id, expr) => {
                let mut ctx = ctx.clone();
                ctx.push(id.clone());
                DeBrujin::Lam(Box::new(expr.debrujin_with(&ctx)))
            }
            Expr::App(expr1, expr2) => DeBrujin::App(
                Box::new(expr1.debrujin_with(ctx)),
                Box::new(expr2.debrujin_with(ctx)),
            ),
            Expr::Var(id) => {
                if let Some(pos) = ctx.iter().position(|x| x == id) {
                    DeBrujin::Var(pos as u32)
                } else {
                    panic!("Unbound variable {}", id)
                }
            }
        }
    }

    fn equivalence(&self, other: &Expr) -> bool {
        self.reduction().debrujin() == other.reduction().debrujin()
    }

    fn substitution(&self, _id: &String, e: &Expr) -> Expr {
        match self {
            Expr::Lam(id, expr) => {
                if id == _id {
                    self.clone()
                } else {
                    let fv = e.fv();
                    if !fv.contains(id) {
                        Expr::Lam(id.clone(), Box::new(expr.substitution(_id, e)))
                    } else {
                        let nid = fresh();
                        Expr::Lam(
                            nid.clone(),
                            Box::new(expr.substitution(id, &Expr::Var(nid)).substitution(id, e)),
                        )
                    }
                }
            }
            Expr::App(e1, e2) => Expr::App(
                Box::new(e1.substitution(_id, e)),
                Box::new(e2.substitution(_id, e)),
            ),
            Expr::Var(id) => {
                if _id == id {
                    e.clone()
                } else {
                    self.clone()
                }
            }
        }
    }

    fn reduction(&self) -> Expr {
        match self {
            Expr::Lam(id, expr) => Expr::Lam(id.clone(), Box::new(expr.reduction())),
            Expr::App(m, n) => {
                let mr = m.reduction();
                let nr = n.reduction();
                if let Expr::Lam(id, mr) = mr {
                    mr.substitution(&id, &nr)
                } else {
                    Expr::App(Box::new(mr), Box::new(nr))
                }
            }
            Expr::Var(_) => self.clone(),
        }
    }

    fn apply(&self, other: &Expr) -> Expr {
        Expr::App(Box::new(self.clone()), Box::new(other.clone()))
    }
}

mod lcterms {
    use super::*;

    pub fn t() -> Expr {
        Expr::Lam(
            "x".to_string(),
            Box::new(Expr::Lam(
                "y".to_string(),
                Box::new(Expr::Var("x".to_string())),
            )),
        )
    }

    pub fn f() -> Expr {
        Expr::Lam(
            "x".to_string(),
            Box::new(Expr::Lam(
                "y".to_string(),
                Box::new(Expr::Var("y".to_string())),
            )),
        )
    }

    pub fn and() -> Expr {
        Expr::Lam(
            "x".to_string(),
            Box::new(Expr::Lam(
                "y".to_string(),
                Box::new(
                    Expr::Var("x".to_string())
                        .apply(&Expr::Var("y".to_string()))
                        .apply(&f()),
                ),
            )),
        )
    }

    pub fn or() -> Expr {
        Expr::Lam(
            "x".to_string(),
            Box::new(Expr::Lam(
                "y".to_string(),
                Box::new(
                    Expr::Var("x".to_string())
                        .apply(&t())
                        .apply(&Expr::Var("y".to_string())),
                ),
            )),
        )
    }

    pub fn not() -> Expr {
        Expr::Lam(
            "x".to_string(),
            Box::new(
                Expr::Var("x".to_string())
                    .apply(&f())
                    .apply(&t())
                    .reduction(),
            ),
        )
    }
}

fn main() {
    let expr = Expr::Lam("x".to_string(), Box::new(Expr::Var("x".to_string())));
    println!("{}", expr.to_string());

    let expr = Expr::App(
        Box::new(Expr::Lam(
            "x".to_string(),
            Box::new(Expr::Var("x".to_string())),
        )),
        Box::new(Expr::Var("y".to_string())),
    );

    println!("{}", expr.to_string());
    println!("{:?}", expr.fv());

    let expr = Expr::App(
        Box::new(Expr::Lam(
            "x".to_string(),
            Box::new(Expr::Var("x".to_string())),
        )),
        Box::new(Expr::Lam(
            "x".to_string(),
            Box::new(Expr::Var("x".to_string())),
        )),
    );

    println!("{}", expr.to_string());
    println!("{}", expr.debrujin().to_string());
    println!("{:?}", expr.fv());
    println!("{}", expr.reduction().to_string());
    println!("{}", lcterms::t().debrujin().to_string());
    println!("{}", lcterms::f().debrujin().to_string());
    println!("{}", lcterms::and().debrujin().to_string());
    let tt = lcterms::and()
        .apply(&lcterms::t())
        .apply(&lcterms::t())
        .reduction();
    println!("{}", tt.equivalence(&lcterms::t()));

    let tf = lcterms::and()
        .apply(&lcterms::t())
        .apply(&lcterms::f())
        .reduction();

    println!("{}", tf.equivalence(&lcterms::f()));

    let ft = lcterms::and()
        .apply(&lcterms::f())
        .apply(&lcterms::t())
        .reduction();

    println!("{}", ft.equivalence(&lcterms::f()));

    let ff = lcterms::and()
        .apply(&lcterms::f())
        .apply(&lcterms::f())
        .reduction();

    println!("{}", ff.equivalence(&lcterms::f()));

    println!("{}", lcterms::or().debrujin().to_string());
    let tt = lcterms::or()
        .apply(&lcterms::t())
        .apply(&lcterms::t())
        .reduction();

    println!("{}", tt.equivalence(&lcterms::t()));

    let tf = lcterms::or()
        .apply(&lcterms::t())
        .apply(&lcterms::f())
        .reduction();

    println!("{}", tf.equivalence(&lcterms::t()));

    let ft = lcterms::or()
        .apply(&lcterms::f())
        .apply(&lcterms::t())
        .reduction();

    println!("{}", ft.equivalence(&lcterms::t()));

    let ff = lcterms::or()
        .apply(&lcterms::f())
        .apply(&lcterms::f())
        .reduction();

    println!("{}", ff.equivalence(&lcterms::f()));

    println!("{}", lcterms::not().debrujin().to_string());

    let t = lcterms::not().apply(&lcterms::t()).reduction();
    println!("{}", t.equivalence(&lcterms::f()));

    let f = lcterms::not().apply(&lcterms::f()).reduction();
    println!("{}", f.equivalence(&lcterms::t()));
    
}
