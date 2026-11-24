-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_map_conj
-- name    : GlobalTheory.StepData.TypeDatum.map_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:32.634108+00:00
-- url     : https://prove2.me/theorems/ef0f6926-befd-4d22-b4ee-68418ad563a4
-- title:
--   Type Datum: map conj
-- statement:
--   The Type Datum construction uses the map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L603-L610
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L603-L610

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
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
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.TypeDatum.map_conj (P : TypeDatum k ι) (F : LatFrame k ι Y) :
    IsOpen ((P.toLevel.map F.conj).J : Set (GL Y k)) ∧ IsCompact ((P.toLevel.map F.conj).J : Set (GL Y k)) ∧
      (P.toLevel.map F.conj).J ≤ stabLat F.bas := by sorry
