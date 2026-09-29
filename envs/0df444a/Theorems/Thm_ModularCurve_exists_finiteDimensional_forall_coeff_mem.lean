-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_coeff_mem
-- name    : ModularCurve.exists_finiteDimensional_forall_coeff_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/9540fbb7-e8b2-5753-a296-b4dc475e7c9b
-- title:
--   Coefficients of ℚ̄-modular functions lie in a number field
-- statement:
--   Let $N$ be a natural number and let $f$ be an element of `modularFunctionFieldBar N`, that is, of the intermediate field `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)` of the Laurent series field $\bar{\mathbb{Q}}(\!(q)\!)$ over $\bar{\mathbb{Q}}$: the subfield generated over $\bar{\mathbb{Q}}$ by the image, under the coefficientwise embedding `coeffEmb` of $\mathbb{Q}(\!(q)\!)$ into $\bar{\mathbb{Q}}(\!(q)\!)$, of `modularFunctionFieldFull N`, the latter being the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the set `divisorExpansions N`. The assertion is that there exists an intermediate field $K$ of $\bar{\mathbb{Q}}$ over $\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$ and such that for every integer $k$ the $k$-th Laurent coefficient of $f$, viewed as an element of $\bar{\mathbb{Q}}(\!(q)\!)$, lies in $K$. No condition on $N$ beyond its being a natural number enters, and the bound $K$ is allowed to depend on $f$.
--
--   The statement says that an element of the function field of $X_0(N)$ over $\bar{\mathbb{Q}}$, presented through its $q$-expansion, has all its coefficients in a single number field. It supplies the finiteness input for the uniform window statements [`ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion`](thm.html#ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion) and [`ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_mem_riemannRochSpace`](thm.html#ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_mem_riemannRochSpace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteDimensional_forall_coeff_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_finiteDimensional_forall_coeff_mem (N : ℕ)
    (f : modularFunctionFieldBar N) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧
      ∀ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ K := by sorry
