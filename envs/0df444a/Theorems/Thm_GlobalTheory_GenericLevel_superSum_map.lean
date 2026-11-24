-- Prove2me | Theorems.Thm_GlobalTheory_GenericLevel_superSum_map
-- name    : GlobalTheory.GenericLevel.superSum_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:09.710865+00:00
-- url     : https://prove2.me/theorems/9424a558-7c60-404b-b892-95d9cbc0c47f
-- title:
--   Generic Level: super Sum map
-- statement:
--   The Generic Level construction uses the super Sum map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean#L69-L74

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
omit [DecidableEq a]

theorem GlobalTheory.GenericLevel.superSum_map {R : Type} [CommRing R] (f : R →+* F) (pos : a → ℕ) (M : Matrix a a R) :
    superSum pos (M.map f) = f (∑ r, ∑ s, if pos s = pos r + 1 then M r s else 0) := by sorry
