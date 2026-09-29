-- Prove2me | Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg
-- name    : ModularCurve.exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/fb926ae2-043d-52a6-9e24-321e11310a1a
-- title:
--   Gauss normalisation of q-expansions on X₀(N)
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $N$ be a positive natural number, and let $f$ be a nonzero element of `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb Q}(\!(\mathfrak q)\!)$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the elements of `modularFunctionFieldFull N`, itself the subfield of $\mathbb Q(\!(\mathfrak q)\!)$ generated over $\mathbb Q$ by `divisorExpansions N`. Assume that for every place $W$ of this field over $\overline{\mathbb Q}$ — that is, every valuation subring of it that contains the image of $\overline{\mathbb Q}$, is not the whole field, and is a principal ideal ring — with $W.\mathrm{ord}\,f<0$, where $\mathrm{ord}$ is minus the logarithm of the associated adic valuation, there exists $a\in A$ with $0<W.\mathrm{ord}\bigl(j-a\bigr)$, $j$ being the element $\mathfrak q^{-1}\cdot\,$`jNumQ` of $\overline{\mathbb Q}(\!(\mathfrak q)\!)$ obtained from `jq` by applying $\overline{\mathbb Q}$-coefficients, and $a$ read in the field via the structure map. Then there is $c\in\overline{\mathbb Q}$, $c\neq0$, such that every Laurent coefficient $(c\cdot f)_k$, $k\in\mathbb Z$, lies in $A$, and for some $n\in\mathbb Z$ the coefficient $(c\cdot f)_n$ is nonzero with $(c\cdot f)_n^{-1}\in A$.
--
--   This is the Gauss normalisation of a function on $X_0(N)_{\overline{\mathbb Q}}$ whose poles lie over $A$-integral values of $j$: after scaling by a constant the $\mathfrak q$-expansion becomes $A$-integral and primitive, some coefficient being a unit of $A$. It strengthens [`ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg`](thm.html#ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg), which it cites, by the unit coefficient, and is used in the integrality statements for $\mathfrak q$-expansions, among them [`ModularCurve.mem_integralCoeffs_of_integral_affineBaseFin`](thm.html#ModularCurve.mem_integralCoeffs_of_integral_affineBaseFin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), W.ord f < 0 →
      ∃ a : A, 0 < W.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      (∀ k : ℤ, (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A) ∧
      ∃ n : ℤ, (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff n ≠ 0 ∧
        ((c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff n)⁻¹ ∈ A := by sorry
