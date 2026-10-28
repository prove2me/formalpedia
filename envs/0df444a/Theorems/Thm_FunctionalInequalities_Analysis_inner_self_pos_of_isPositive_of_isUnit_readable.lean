-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inner_self_pos_of_isPositive_of_isUnit_readable
-- name    : FunctionalInequalities.Analysis.inner_self_pos_of_isPositive_of_isUnit_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:43.798423+00:00
-- url     : https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb
-- title:
--   Strict Positivity Of A Positive Operator Unit
-- statement:
--   This statement proves that a positive invertible operator is strictly positive.
--
--   Let E be a finite-dimensional real inner-product space, let ι be a finite index type with decidable equality, and let b be an orthonormal basis of E indexed by ι. Let T be a continuous linear endomorphism. Assume T is positive in the operator sense and is a unit. Then every nonzero v∈E satisfies
--
--   $$\langle Tv,v\rangle>0.$$
--
--   This provides the converse positivity fact needed when transferring positive-definite matrix properties to operators in orthonormal coordinates.
--
--   **Formalization Note** Finite dimensionality and the chosen finite orthonormal basis are explicit hypotheses of the Lean statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_self_pos_of_isPositive_of_isUnit (b : OrthonormalBasis ι ℝ E)
--       (T : E →L[ℝ] E) (hpos : T.IsPositive) (hunit : IsUnit T)
--       {v : E} (hv : v ≠ 0) : 0 < ⟪T v, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   [Source excerpt, lines 151–153](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/Coordinates.lean#L151-L153) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/Coordinates.lean#L150-L165 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.Coordinates`, declaration `FunctionalInequalities.Analysis.inner_self_pos_of_isPositive_of_isUnit`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates

open scoped RealInnerProductSpace MatrixOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.inner_self_pos_of_isPositive_of_isUnit_readable (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E) (hpos : T.IsPositive) (hunit : IsUnit T)
    {v : E} (hv : v ≠ 0) : 0 < ⟪T v, v⟫ := by sorry
