-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_exists_subgroup_invariant
-- name    : GlobalTheory.SplitWeil.HaarFactor.exists_subgroup_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:16.038585+00:00
-- url     : https://prove2.me/theorems/1b5b6ff5-98f9-4d00-8c70-0f41cb01eaf9
-- title:
--   Haar Factor: exists subgroup invariant
-- statement:
--   The Haar Factor construction uses the exists subgroup invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L55-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L55-L75

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

theorem GlobalTheory.SplitWeil.HaarFactor.exists_subgroup_invariant
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) :
    ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧
      ∀ u ∈ U, ∀ z : X₀ × A, G (z.1, z.2 + u) = G z := by sorry
