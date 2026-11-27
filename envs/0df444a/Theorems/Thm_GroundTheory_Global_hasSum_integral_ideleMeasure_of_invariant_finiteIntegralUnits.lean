-- Prove2me | Theorems.Thm_GroundTheory_Global_hasSum_integral_ideleMeasure_of_invariant_finiteIntegralUnits
-- name    : GroundTheory.Global.hasSum_integral_ideleMeasure_of_invariant_finiteIntegralUnits
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:44.870614+00:00
-- url     : https://prove2.me/theorems/25bd4917-6988-52f4-a378-f02af657351b
-- title:
--   Global: has Sum integral idele Measure of invariant finite Integral Units
-- statement:
--   The Global construction uses the has Sum integral idele Measure of invariant finite Integral Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureCosets.lean#L83-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureCosets.lean#L83-L93

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem GroundTheory.Global.hasSum_integral_ideleMeasure_of_invariant_finiteIntegralUnits {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : IdeleGroup K → E}
    (hFi : Integrable F (ideleMeasure K))
    (hF : ∀ x : IdeleGroup K, ∀ w ∈ finiteIntegralUnits K,
      F (x * (IdeleGroup.prodEquiv K).symm (1, w)) = F x) :
    HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K ↦
        ∫ a, F ((IdeleGroup.prodEquiv K).symm (a, c.out)) ∂infiniteIdeleMeasure K)
      (∫ x, F x ∂ideleMeasure K) := by sorry
