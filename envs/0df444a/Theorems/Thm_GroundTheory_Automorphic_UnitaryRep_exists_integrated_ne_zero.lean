-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_exists_integrated_ne_zero
-- name    : GroundTheory.Automorphic.UnitaryRep.exists_integrated_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:34.568364+00:00
-- url     : https://prove2.me/theorems/13c95af0-a89d-48b3-a43b-9b63afacbbb5
-- title:
--   Unitary Rep: exists integrated ne zero
-- statement:
--   The Unitary Rep construction uses the exists integrated ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L83-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L83-L129

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

theorem GroundTheory.Automorphic.UnitaryRep.exists_integrated_ne_zero [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {v : H} (hv : v ≠ 0) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, π.integrated μ (ccToL1 μ f) v ≠ 0 := by sorry
