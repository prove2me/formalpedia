-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_flatSB_isLocallyConstant_indicator
-- name    : GlobalTheory.LocFlat.flatSB_isLocallyConstant_indicator
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:42.339804+00:00
-- url     : https://prove2.me/theorems/6935d679-772c-4aae-8c54-cd9e478fcf76
-- title:
--   Loc Flat: flat SB is Locally Constant indicator
-- statement:
--   The Loc Flat construction uses the flat SB is Locally Constant indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat

theorem GlobalTheory.LocFlat.flatSB_isLocallyConstant_indicator {X : Type*} [TopologicalSpace X] {W : Set X} (hW : IsClopen W)
    (a : ℂ) : IsLocallyConstant (W.indicator fun _ => a) := by sorry
