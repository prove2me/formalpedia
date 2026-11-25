-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_finite_setOf_isEquivalent
-- name    : GroundTheory.Automorphic.UnitaryRep.finite_setOf_isEquivalent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:44.420063+00:00
-- url     : https://prove2.me/theorems/e24c7068-9819-4064-b26f-351dc5b4bc51
-- title:
--   Unitary Rep: finite set Of is Equivalent
-- statement:
--   The Unitary Rep construction uses the finite set Of is Equivalent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L479-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L479-L519

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

theorem GroundTheory.Automorphic.UnitaryRep.finite_setOf_isEquivalent
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f)))
    {ι : Type*} {V : ι → Submodule ℂ H} [∀ i, CompleteSpace (V i)]
    (hinv : ∀ i, π.IsInvariant (V i))
    (hV : OrthogonalFamily ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ)
    {σ : UnitaryRep G K} (hσ : σ.IsIrreducible) :
    {i | (π.restrict (V i) (hinv i)).IsEquivalent σ}.Finite := by sorry
