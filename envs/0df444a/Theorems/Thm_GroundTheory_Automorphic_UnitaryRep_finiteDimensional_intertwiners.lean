-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_finiteDimensional_intertwiners
-- name    : GroundTheory.Automorphic.UnitaryRep.finiteDimensional_intertwiners
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:15.432945+00:00
-- url     : https://prove2.me/theorems/f7295f13-9994-4bf6-8946-7c88ddff1416
-- title:
--   Unitary Rep: finite Dimensional intertwiners
-- statement:
--   The Unitary Rep construction uses the finite Dimensional intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L403-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L403-L477

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

theorem GroundTheory.Automorphic.UnitaryRep.finiteDimensional_intertwiners
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f)))
    {σ : UnitaryRep G K} (hσ : σ.IsIrreducible) :
    FiniteDimensional ℂ (σ.intertwiners π) := by sorry
