-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_apply_eq_integral
-- name    : GroundTheory.Automorphic.UnitaryRep.integrated_apply_eq_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:21.772194+00:00
-- url     : https://prove2.me/theorems/a02a6c7d-23fe-4f57-9b43-295f0a499ee4
-- title:
--   Unitary Rep: integrated apply eq integral
-- statement:
--   The Unitary Rep construction uses the integrated apply eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L114-L119

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
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
open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)

theorem GroundTheory.Automorphic.UnitaryRep.integrated_apply_eq_integral (f : G →₁[μ] ℂ) (v : H)
    (hint : Integrable (fun g => f g • π g v) μ) :
    π.integrated μ f v = ∫ g, f g • π g v ∂μ := by sorry
