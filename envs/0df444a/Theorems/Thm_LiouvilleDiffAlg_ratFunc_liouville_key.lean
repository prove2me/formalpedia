-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_ratFunc_liouville_key
-- name    : LiouvilleDiffAlg.ratFunc_liouville_key
-- status  : Open
-- author  : @vebis
-- created : 2026-10-01T11:41:26.253986+00:00
-- url     : https://prove2.me/theorems/8d0175b1-bbfd-4b1b-bcd2-64b8f4b3a22a
-- title:
--   Pole analysis for logarithmic derivatives in K(X)
-- statement:
--   Throughout, $K$ is a field of characteristic zero with a derivation $D$, and $K(X)$ is the field of rational functions in one variable over $K$, equipped with a derivation (also written $D$) that extends the derivation of $K$. Assume that the derivative of every polynomial in $K[X]$ is a polynomial, and let $\mathcal E$ be a property of polynomials (the "exceptional" ones) such that every monic irreducible $p\in K[X]$ not in $\mathcal E$ does not divide its own derivative $Dp$. Let $h\in K$, let $c_1,\dots,c_n\in K$ be constants ($Dc_i=0$), let $u_1,\dots,u_n\in K(X)$ be nonzero and $v\in K(X)$, and suppose
--
--   $$h=\sum_{i=1}^n c_i\,\frac{Du_i}{u_i}+Dv.$$
--
--   Then there are nonzero $a_1,\dots,a_n\in K$, a finite set $E$ of monic irreducible exceptional polynomials, constants $C_p\in K$ ($p\in E$) and polynomials $A,B$ with $B\ne0$ and $v=A/B$, such that every monic irreducible factor of $B$ is exceptional and
--
--   $$h=\sum_{i=1}^n c_i\frac{Da_i}{a_i}+\sum_{p\in E}C_p\,\frac{Dp}{p}+Dv.$$
--
--   In words: logarithmic derivatives of rational functions only have simple poles, so in such an identity the poles of $v$ and the non-exceptional prime factors of the $u_i$ are forced to disappear.
--
--   **Formalization Note** The constants $C_p$ are returned as a function on all polynomials with $DC_p=0$.
-- source:
--   Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972 (proof of Liouville's theorem by induction on an elementary tower); Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Wikipedia, "Liouville's theorem (differential algebra)", oldid=1349223559, section "Basic theorem"

import Mathlib

open scoped Differential
open Polynomial

namespace LiouvilleDiffAlg

theorem ratFunc_liouville_key {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (hpoly : ∀ r : K[X], ∃ q : K[X], (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) q)
    (Exc : K[X] → Prop)
    (hExc : ∀ p q : K[X], Monic p → Irreducible p → ¬ Exc p →
      (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) q → ¬ p ∣ q)
    {n : ℕ} (c : Fin n → K) (hc : ∀ i, (c i)′ = 0) (h : K)
    (u : Fin n → RatFunc K) (hu : ∀ i, u i ≠ 0) (v : RatFunc K)
    (hfe : algebraMap K (RatFunc K) h = ∑ i, algebraMap K (RatFunc K) (c i) * ((u i)′ / u i) + v′) :
    ∃ (a : Fin n → K) (E : Finset K[X]) (C : K[X] → K) (A B : K[X]),
      (∀ i, a i ≠ 0) ∧ (∀ p ∈ E, Monic p ∧ Irreducible p ∧ Exc p) ∧ (∀ p, (C p)′ = 0) ∧
      B ≠ 0 ∧ v = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) B ∧
      (∀ p, Monic p → Irreducible p → p ∣ B → Exc p) ∧
      algebraMap K (RatFunc K) h =
        ∑ i, algebraMap K (RatFunc K) (c i) * ((algebraMap K (RatFunc K) (a i))′ / algebraMap K (RatFunc K) (a i)) +
        ∑ p ∈ E, algebraMap K (RatFunc K) (C p) * ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p) + v′ := by sorry

end LiouvilleDiffAlg
