-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_IntEntry_fill_add_single
-- name    : GlobalTheory.PartRed.IntEntry.fill_add_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:37.762111+00:00
-- url     : https://prove2.me/theorems/76ee468f-51e3-4a2f-8f65-97b46220488f
-- title:
--   Int Entry: fill add single
-- statement:
--   The Int Entry construction uses the fill add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L18-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry

theorem GlobalTheory.PartRed.IntEntry.fill_add_single {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
    (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) (a : k) :
    fillAt β E I (x + Matrix.single e.1 e.2 a) y = fillAt β E I x y + Matrix.single e.1 e.2 a := by sorry
