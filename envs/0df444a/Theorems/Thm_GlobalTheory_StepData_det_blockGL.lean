-- Prove2me | Theorems.Thm_GlobalTheory_StepData_det_blockGL
-- name    : GlobalTheory.StepData.det_blockGL
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:58.694124+00:00
-- url     : https://prove2.me/theorems/b6dc90a8-15eb-4ab2-9007-37508e9cd951
-- title:
--   Step Data: det block GL
-- statement:
--   The Step Data construction uses the det block GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L174-L177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.det_blockGL (g : GL a k) (B : Matrix a t k) (D : GL t k) :
    Matrix.GeneralLinearGroup.det (blockGL g B D) =
      Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det D := by sorry
