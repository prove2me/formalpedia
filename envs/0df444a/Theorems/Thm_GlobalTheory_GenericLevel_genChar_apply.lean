-- Prove2me | Theorems.Thm_GlobalTheory_GenericLevel_genChar_apply
-- name    : GlobalTheory.GenericLevel.genChar_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:19.620591+00:00
-- url     : https://prove2.me/theorems/85f7c8dc-1834-4511-ac86-96a723a47dbc
-- title:
--   Generic Level: gen Char apply
-- statement:
--   The Generic Level construction uses the gen Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean#L82-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.GenericLevel
variable {F a : Type} [Field F] [Fintype a] [DecidableEq a]

theorem GlobalTheory.GenericLevel.genChar_apply (φ : AddChar F Circle) (pos : a → ℕ) (g : upperUnip F pos) :
    ((genChar φ pos g : ℂˣ) : ℂ) = φ (superSum pos ((g : GL a F) : Matrix a a F)) := by sorry
