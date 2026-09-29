-- Prove2me | Theorems.Thm_ModularCurve_exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
-- name    : ModularCurve.exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/af2c1192-1dc3-5ca1-8241-cae8ebd81df1
-- title:
--   Bounded denominators for the Fricke transform on X₀(p)
-- statement:
--   Let $p$ be a prime and $n$ a natural number. Let $f$ be an element of `modularFunctionFieldBar (1 * p)`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the function field `modularFunctionFieldFull (1 * p)` (itself generated over $\mathbb{Q}$ by the divisor expansions of level $1\cdot p$). Assume $f$ lies in the Riemann–Roch space of the divisor $n\cdot(\bar\infty)$, where $\bar\infty$ is the place `cuspInftyBar (1 * p)` (the $q$-adic place attached to the $j$-expansion) and membership means that for every place $v$ of this field over $\overline{\mathbb{Q}}$ the adic valuation of $f$ at $v$ is at most $\exp$ of the coefficient of the divisor at $v$; assume also $f \neq 0$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$. Then there exists $c \in \overline{\mathbb{Q}}$, $c \neq 0$, such that for every $k \in \mathbb{Z}$ the product of $c$ with the $k$-th Laurent coefficient of the image of $f$ under `frickeInvolutionBar (1 * p)` lies in $A$. Unlike the corresponding statement at $\bar\infty$ that the proof cites, no coefficient is asserted to be a unit of $A$.
--
--   This is the bounded-denominator, or $q$-expansion-principle, statement at the cusp $0$ of $X_0(p)$: the expansion at $\infty$ of the Fricke transform of a function with poles only at $\bar\infty$ has bounded denominators along any valuation ring of $\overline{\mathbb{Q}}$ above $p$. It feeds the integrality estimates used in the analysis of the multiplicative covering and its charts, and is the twin of the corresponding bound at $\bar\infty$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar.lean

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
    (p : ℕ) [Fact p.Prime] (n : ℕ) (f : modularFunctionFieldBar (1 * p))
    (hf : f ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ))) (hf0 : f ≠ 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      ∀ k : ℤ, c * ((frickeInvolutionBar (1 * p) f : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := by sorry
