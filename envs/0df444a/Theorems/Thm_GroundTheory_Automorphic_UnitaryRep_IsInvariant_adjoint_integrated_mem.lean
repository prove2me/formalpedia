-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_adjoint_integrated_mem
-- name    : GroundTheory.Automorphic.UnitaryRep.IsInvariant.adjoint_integrated_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:35.436682+00:00
-- url     : https://prove2.me/theorems/5522eea3-24dd-419d-8ecf-96bb8e8d0631
-- title:
--   Is Invariant: adjoint integrated mem
-- statement:
--   The Is Invariant construction uses the adjoint integrated mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L55-L64

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

theorem GroundTheory.Automorphic.UnitaryRep.IsInvariant.adjoint_integrated_mem {V : Submodule ℂ H} (hcl : IsClosed (V : Set H))
    (hV : π.IsInvariant V) (f : G →₁[μ] ℂ) {v : H} (hv : v ∈ V) :
    adjoint (π.integrated μ f) v ∈ V := by sorry
