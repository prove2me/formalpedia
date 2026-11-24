-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_ind_mem
-- name    : GlobalTheory.SplitWeil.HaarFactor.ind_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:32.339944+00:00
-- url     : https://prove2.me/theorems/6f8cdec7-34cc-42a9-baec-a68363ce3a97
-- title:
--   Haar Factor: ind mem
-- statement:
--   The Haar Factor construction uses the ind mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L39-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]

theorem GlobalTheory.SplitWeil.HaarFactor.ind_mem {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A)) :
    (U : Set A).indicator (fun _ => (1 : ℂ)) ∈ SB A := by sorry
