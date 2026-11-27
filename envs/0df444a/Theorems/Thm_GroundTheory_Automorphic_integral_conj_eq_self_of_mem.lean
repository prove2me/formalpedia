-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_integral_conj_eq_self_of_mem
-- name    : GroundTheory.Automorphic.integral_conj_eq_self_of_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:06.643273+00:00
-- url     : https://prove2.me/theorems/3f24464e-7563-44c9-bf08-e0f304923890
-- title:
--   Automorphic: integral conj eq self of mem
-- statement:
--   The Automorphic construction uses the integral conj eq self of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L96-L102

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem GroundTheory.Automorphic.integral_conj_eq_self_of_mem (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    {K : Subgroup G} (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : G → E) :
    ∫ y, F (k * y * k⁻¹) ∂μ = ∫ y, F y ∂μ := by sorry
