-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_exists_isHilbertSum_isIrreducible
-- name    : GroundTheory.Automorphic.UnitaryRep.exists_isHilbertSum_isIrreducible
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:37.977175+00:00
-- url     : https://prove2.me/theorems/af470515-cf15-5fd5-805c-d2a6155d8251
-- title:
--   Unitary Rep: exists is Hilbert Sum is Irreducible
-- statement:
--   The Unitary Rep construction uses the exists is Hilbert Sum is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L392-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L392-L401

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

theorem GroundTheory.Automorphic.UnitaryRep.exists_isHilbertSum_isIrreducible
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f))) :
    ∃ s : Set (Submodule ℂ H), ∃ _ : ∀ V : s, CompleteSpace (V : Submodule ℂ H),
      ∃ hinv : ∀ V : s, π.IsInvariant V,
      IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ H)) (fun V => (V : Submodule ℂ H).subtypeₗᵢ) ∧
      ∀ V : s, (π.restrict V (hinv V)).IsIrreducible := by sorry
