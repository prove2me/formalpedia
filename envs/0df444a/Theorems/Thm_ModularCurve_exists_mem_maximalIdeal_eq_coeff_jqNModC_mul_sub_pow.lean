-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_maximalIdeal_eq_coeff_jqNModC_mul_sub_pow
-- name    : ModularCurve.exists_mem_maximalIdeal_eq_coeff_jqNModC_mul_sub_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/e0e6a78d-53b7-59f7-bcf2-efa78ca9b917
-- title:
--   Coefficients of j(mathsf q^{qn})-j(mathsf qⁿ)^q lie in the maximal ideal
-- statement:
--   Let $k_0$ be a field and $A_0 \subseteq k_0$ a valuation subring, so that $A_0$ is a local ring with maximal ideal $\mathfrak m_{A_0}$; let $q$ be a prime and assume that the image of $q$ under $\mathbb N \to A_0$ lies in $\mathfrak m_{A_0}$; let $n$ be a nonzero natural number (with $qn$ likewise nonzero). Here `jqNModC k₀ N` denotes the Laurent series over $k_0$ obtained from `jqModC k₀`, the product of the monomial $\mathsf q^{-1}$ with the image in $k_0$ of the integral power series `jNum`, by the ring homomorphism `qExpand` that multiplies all exponents by $N$, i.e. the substitution $\mathsf q \mapsto \mathsf q^{N}$. The assertion is that for every integer $m$ there exists $a \in \mathfrak m_{A_0}$ whose image in $k_0$ equals the coefficient of index $m$ of the Laurent series $\,$`jqNModC k₀ (q * n)` $-$ `(jqNModC k₀ n) ^ q`.
--
--   This records the integrality of the Frobenius defect of the $q$-expansion of $j$: the difference between the $qn$-expansion and the $q$-th power of the $n$-expansion has all coefficients divisible by $q$, read coefficientwise inside a valuation subring in which $q$ is not a unit. It is used in the analysis of Tate points and of the action of level automorphisms on full-level modular curves, in the two statements on cyclic quotients of $j$ that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_maximalIdeal_eq_coeff_jqNModC_mul_sub_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_mem_maximalIdeal_eq_coeff_jqNModC_mul_sub_pow
    (k₀ : Type) [Field k₀] (A₀ : ValuationSubring k₀)
    (q : ℕ) [Fact q.Prime] (hq𝔪 : ((q : ↥A₀)) ∈ IsLocalRing.maximalIdeal ↥A₀)
    (n : ℕ) [NeZero n] [NeZero (q * n)] :
    ∀ m : ℤ, ∃ a ∈ IsLocalRing.maximalIdeal ↥A₀,
      ((a : ↥A₀) : k₀) = (jqNModC k₀ (q * n) - (jqNModC k₀ n) ^ q).coeff m := by sorry
