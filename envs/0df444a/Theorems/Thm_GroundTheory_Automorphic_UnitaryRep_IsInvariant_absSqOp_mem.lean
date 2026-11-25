-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_absSqOp_mem
-- name    : GroundTheory.Automorphic.UnitaryRep.IsInvariant.absSqOp_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:35.362801+00:00
-- url     : https://prove2.me/theorems/74674526-3ec1-4a03-9861-f4b5e4c6499f
-- title:
--   Is Invariant: abs Sq Op mem
-- statement:
--   The Is Invariant construction uses the abs Sq Op mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L66-L69

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

theorem GroundTheory.Automorphic.UnitaryRep.IsInvariant.absSqOp_mem {V : Submodule ℂ H} (hcl : IsClosed (V : Set H))
    (hV : π.IsInvariant V) (f : G →₁[μ] ℂ) {v : H} (hv : v ∈ V) :
    π.absSqOp μ f v ∈ V := by sorry
