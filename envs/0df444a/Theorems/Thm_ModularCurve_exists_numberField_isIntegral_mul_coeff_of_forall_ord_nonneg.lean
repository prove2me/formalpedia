-- Prove2me | Theorems.Thm_ModularCurve_exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg
-- name    : ModularCurve.exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/2b74fc9b-c1e9-5cb0-8a68-73a69279f7b4
-- title:
--   Coefficients in one number field with bounded denominators
-- statement:
--   Fix $N \geq 1$ and let $f$ lie in `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images under `coeffEmb` of the elements of `modularFunctionFieldFull N`, itself the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `divisorExpansions N`. Write $j$ for the element of that field given by the coefficientwise image of $jq = q^{-1}\cdot jNumQ$. The hypothesis is that for every place $v$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ — that is, every valuation subring containing $\overline{\mathbb{Q}}$, distinct from the whole field and a principal ideal ring — the inequality $0 \le v.\mathrm{ord}(j)$ implies $0 \le v.\mathrm{ord}(f)$, where $\mathrm{ord}$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation. The conclusion asserts the existence of an intermediate field $K$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, together with a natural number $d \neq 0$, such that for every $n \in \mathbb{Z}$ the $n$-th Laurent coefficient of $f$ lies in $K$ and $d$ times that coefficient is integral over $\mathbb{Z}$.
--
--   This is the rationality and bounded-denominator statement for $q$-expansions of functions on $X_0(N)$ over $\overline{\mathbb{Q}}$ whose poles are confined to the cusps: all Fourier coefficients lie in a single number field and admit a common denominator. It feeds into [`ModularCurve.exists_uniform_adapted_basis`](thm.html#ModularCurve.exists_uniform_adapted_basis), where a basis with uniform integrality properties is extracted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg
    (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N)
    (hf : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) →
        0 ≤ v.ord f) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (d : ℕ), FiniteDimensional ℚ K ∧ d ≠ 0 ∧
      ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K ∧
        IsIntegral ℤ ((d : AlgebraicClosure ℚ) * (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n) := by sorry
