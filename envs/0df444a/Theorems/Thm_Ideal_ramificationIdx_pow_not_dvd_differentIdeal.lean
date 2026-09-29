-- Prove2me | Theorems.Thm_Ideal_ramificationIdx_pow_not_dvd_differentIdeal
-- name    : Ideal.ramificationIdx_pow_not_dvd_differentIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/b5767fca-aa6a-582d-9743-459a06bedd22
-- title:
--   Tame ramification: P^e does not divide the different
-- statement:
--   Let $A$ and $B$ be commutative rings with an $A$-algebra structure on $B$, both Dedekind domains, with $B$ finite and torsion-free as an $A$-module, and assume the extension of fraction fields $\operatorname{FractionRing}(B)/\operatorname{FractionRing}(A)$ — taken with the algebra structure `FractionRing.liftAlgebra` — is separable. Let $\mathfrak p$ be a maximal ideal of $A$ with $\mathfrak p \neq \bot$, and let $\mathfrak P$ be a maximal ideal of $B$ lying over $\mathfrak p$, such that the residue field extension $(B/\mathfrak P)/(A/\mathfrak p)$ is separable. Write $e =$ `Ideal.ramificationIdx' p P` for the ramification index of $\mathfrak P$ over $\mathfrak p$, and assume that the image of the natural number $e$ under the canonical map $\mathbb N \to A/\mathfrak p$ is nonzero, i.e. the residue characteristic does not divide $e$ (tame ramification). The conclusion is that $\mathfrak P^{e}$ does not divide the different ideal $\mathfrak D_{B/A} =$ `differentIdeal A B`, as ideals of $B$.
--
--   This is the upper bound half of the classical formula for the exponent of a tamely ramified prime in the different; combined with the divisibility $\mathfrak P^{e-1} \mid \mathfrak D_{B/A}$ it gives that the exponent is exactly $e-1$. It is used in the project's bound on the degree of a number field tamely ramified over a fixed small prime, via [`Algebra.exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero`](thm.html#Algebra.exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_ramificationIdx_pow_not_dvd_differentIdeal.lean

import Mathlib.RingTheory.DedekindDomain.Different

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ideal.ramificationIdx_pow_not_dvd_differentIdeal (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
    [@Algebra.IsSeparable (FractionRing A) (FractionRing B) _ _
      (FractionRing.liftAlgebra A (FractionRing B))]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((Ideal.ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ Ideal.ramificationIdx' p P ∣ differentIdeal A B := by sorry
