-- Prove2me | Theorems.Thm_GlobalTheory_GenericLevel_exists_residueChar
-- name    : GlobalTheory.GenericLevel.exists_residueChar
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:05.426359+00:00
-- url     : https://prove2.me/theorems/0f1b2d32-68cb-4d6a-9b9e-e93980e9bc59
-- title:
--   Generic Level: exists residue Char
-- statement:
--   The Generic Level construction uses the exists residue Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean#L13-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean#L13-L43

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.GenericLevel.exists_residueChar {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ φ : AddChar 𝓀[k] Circle, ∀ x : 𝒪[k],
      φ (IsLocalRing.residue 𝒪[k] x) = ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) := by sorry
