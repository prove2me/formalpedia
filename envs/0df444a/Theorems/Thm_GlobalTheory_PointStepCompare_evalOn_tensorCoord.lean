-- Prove2me | Theorems.Thm_GlobalTheory_PointStepCompare_evalOn_tensorCoord
-- name    : GlobalTheory.PointStepCompare.evalOn_tensorCoord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:57.120771+00:00
-- url     : https://prove2.me/theorems/1d545755-8d26-4819-90aa-1ceee063b864
-- title:
--   Point Step Compare: eval On tensor Coord
-- statement:
--   The Point Step Compare construction uses the eval On tensor Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean#L26-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PointStepCompare
open NumberField Matrix
open scoped MatrixOrder
variable {Y : Type} [AddCommGroup Y] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)

theorem GlobalTheory.PointStepCompare.evalOn_tensorCoord (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) :
    evalOn b B (tensorCoord b x y) = B x y := by sorry
