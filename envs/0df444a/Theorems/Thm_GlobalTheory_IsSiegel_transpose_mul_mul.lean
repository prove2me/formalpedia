-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_transpose_mul_mul
-- name    : GlobalTheory.IsSiegel.transpose_mul_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:17.379078+00:00
-- url     : https://prove2.me/theorems/c99203fa-d553-4de6-bc01-d5e8440fd245
-- title:
--   Is Siegel: transpose mul mul
-- statement:
--   The Is Siegel construction uses the transpose mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L71-L79

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

theorem GlobalTheory.IsSiegel.transpose_mul_mul {σ : Matrix ι ι ℂ} (h : IsSiegel σ) {P : Matrix ι ι ℝ}
    (hP : P.det ≠ 0) : IsSiegel ((P.map ofReal)ᵀ * σ * P.map ofReal) := by sorry
