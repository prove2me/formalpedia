-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_exists_isMinimal_le
-- name    : GroundTheory.Automorphic.UnitaryRep.exists_isMinimal_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:57.3302+00:00
-- url     : https://prove2.me/theorems/8277b7ed-799b-4147-898b-24f12a357e5a
-- title:
--   Unitary Rep: exists is Minimal le
-- statement:
--   The Unitary Rep construction uses the exists is Minimal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L206-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L206-L334

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

theorem GroundTheory.Automorphic.UnitaryRep.exists_isMinimal_le [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f)))
    {W : Submodule ℂ H} (hWcl : IsClosed (W : Set H)) (hWinv : π.IsInvariant W) (hW : W ≠ ⊥) :
    ∃ U, π.IsMinimal U ∧ U ≤ W := by sorry
