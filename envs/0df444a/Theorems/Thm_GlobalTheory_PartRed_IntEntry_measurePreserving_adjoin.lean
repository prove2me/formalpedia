-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_IntEntry_measurePreserving_adjoin
-- name    : GlobalTheory.PartRed.IntEntry.measurePreserving_adjoin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:03.006816+00:00
-- url     : https://prove2.me/theorems/046467dc-c79c-439a-88ff-6b634b8f1eb7
-- title:
--   Int Entry: measure Preserving adjoin
-- statement:
--   The Int Entry construction uses the measure Preserving adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L32-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L32-L66

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

theorem GlobalTheory.PartRed.IntEntry.measurePreserving_adjoin {ι X : Type} [DecidableEq ι] [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    (I : Finset ι) (e : ι) (he : e ∉ I) :
    MeasurePreserving
      (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1)
      (ν.prod (Measure.pi fun _ : I => ν)) (Measure.pi fun _ : ↥(insert e I : Finset ι) => ν) := by sorry
