-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_ratFunc_pole_free
-- name    : LiouvilleDiffAlg.ratFunc_pole_free
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T11:41:06.739067+00:00
-- url     : https://prove2.me/theorems/c99ce1a4-e462-48a6-aa2e-d1e0b4e5bcff
-- title:
--   Derivative with a simple pole forces regularity
-- statement:
--   Throughout, $K$ is a field of characteristic zero with a derivation $D$, and $K(X)$ is the field of rational functions in one variable over $K$, equipped with a derivation (also written $D$) that extends the derivation of $K$. Let $p\in K[X]$ be an irreducible polynomial and put $Dp=q$ with $q\in K[X]$ (the derivative of a polynomial is a polynomial), and assume $p\nmid q$. Let $x\in K(X)$ and suppose the derivative $Dx$ has at most a simple pole at $p$, i.e. $Dx = r/(p\,s)$ for some polynomials $r,s$ with $p\nmid s$. Then $x$ has no pole at $p$: there are polynomials $a,b$ with $p\nmid b$ and $x=a/b$.
--
--   This is the local statement behind the fact that in the logarithmic derivative of a rational function, all poles are simple: a function with a pole of order $m\ge1$ at a prime $p$ not dividing its own derivative has a derivative with a pole of order exactly $m+1$.
--
--   **Formalization Note** The hypothesis `hpoly` states that the derivative of every polynomial is again a polynomial; the conclusion is phrased as $x\cdot b=a$ in $K(X)$.
-- source:
--   Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972 (proof of Liouville's theorem by induction on an elementary tower); Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Wikipedia, "Liouville's theorem (differential algebra)", oldid=1349223559, section "Basic theorem"

import Mathlib

open scoped Differential
open Polynomial

namespace LiouvilleDiffAlg

theorem ratFunc_pole_free {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (hpoly : ∀ r : K[X], ∃ q : K[X], (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) q)
    {p q : K[X]} (hp : Irreducible p) (hq : (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) q)
    (hpq : ¬ p ∣ q) (x : RatFunc K)
    (hx : ∃ r s : K[X], ¬ p ∣ s ∧ x′ * algebraMap K[X] (RatFunc K) (p * s) = algebraMap K[X] (RatFunc K) r) :
    ∃ a b : K[X], ¬ p ∣ b ∧ x * algebraMap K[X] (RatFunc K) b = algebraMap K[X] (RatFunc K) a := by sorry

end LiouvilleDiffAlg
