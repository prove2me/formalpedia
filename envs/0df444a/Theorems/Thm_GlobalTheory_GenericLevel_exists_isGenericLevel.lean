-- Prove2me | Theorems.Thm_GlobalTheory_GenericLevel_exists_isGenericLevel
-- name    : GlobalTheory.GenericLevel.exists_isGenericLevel
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:33.223895+00:00
-- url     : https://prove2.me/theorems/011a261f-8a07-4be3-b520-d327f1feb9d9
-- title:
--   Generic Level: exists is Generic Level
-- statement:
--   The Generic Level construction uses the exists is Generic Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean#L87-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean#L87-L113

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

theorem GlobalTheory.GenericLevel.exists_isGenericLevel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ κ l : ℕ,
      ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsGenericLevel ψ ϖ P := by sorry
