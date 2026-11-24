-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_exists_eq_transpose_mul_diagonal_mul
-- name    : GlobalTheory.IsSiegel.exists_eq_transpose_mul_diagonal_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:41.565369+00:00
-- url     : https://prove2.me/theorems/bc73d6b2-b521-4c61-9d51-5869421a9891
-- title:
--   Is Siegel: exists eq transpose mul diagonal mul
-- statement:
--   The Is Siegel construction uses the exists eq transpose mul diagonal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L16-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L16-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open scoped MatrixOrder

theorem GlobalTheory.IsSiegel.exists_eq_transpose_mul_diagonal_mul {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    ∃ P : Matrix ι ι ℝ, P.det ≠ 0 ∧ ∃ t : ι → ℂ, (∀ i, 0 < (t i).im) ∧
      σ = (P.map ofReal)ᵀ * diagonal t * P.map ofReal := by sorry
