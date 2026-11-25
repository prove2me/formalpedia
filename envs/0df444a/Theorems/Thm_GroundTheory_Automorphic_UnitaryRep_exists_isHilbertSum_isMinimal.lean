-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_exists_isHilbertSum_isMinimal
-- name    : GroundTheory.Automorphic.UnitaryRep.exists_isHilbertSum_isMinimal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:53.609413+00:00
-- url     : https://prove2.me/theorems/d7b7d42d-62e9-4a81-a6d3-8fc490c9c479
-- title:
--   Unitary Rep: exists is Hilbert Sum is Minimal
-- statement:
--   The Unitary Rep construction uses the exists is Hilbert Sum is Minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L341-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L341-L390

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

theorem GroundTheory.Automorphic.UnitaryRep.exists_isHilbertSum_isMinimal
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f))) :
    ∃ s : Set (Submodule ℂ H), ∃ _ : ∀ V : s, CompleteSpace (V : Submodule ℂ H),
      (∀ V ∈ s, π.IsMinimal V) ∧
      IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ H)) fun V => (V : Submodule ℂ H).subtypeₗᵢ := by sorry
