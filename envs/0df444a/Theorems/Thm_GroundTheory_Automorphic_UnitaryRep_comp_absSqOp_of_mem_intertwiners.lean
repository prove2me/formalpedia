-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_absSqOp_of_mem_intertwiners
-- name    : GroundTheory.Automorphic.UnitaryRep.comp_absSqOp_of_mem_intertwiners
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:48.044626+00:00
-- url     : https://prove2.me/theorems/e2e6b598-a194-42dc-8c8e-9ee78d393bd1
-- title:
--   Unitary Rep: comp abs Sq Op of mem intertwiners
-- statement:
--   The Unitary Rep construction uses the comp abs Sq Op of mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L71-L81

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

theorem GroundTheory.Automorphic.UnitaryRep.comp_absSqOp_of_mem_intertwiners {σ : UnitaryRep G K} {T : K →L[ℂ] H}
    (hT : T ∈ σ.intertwiners π) (f : G →₁[μ] ℂ) :
    T ∘L σ.absSqOp μ f = π.absSqOp μ f ∘L T := by sorry
