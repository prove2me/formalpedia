-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_ideleMeasure_eq_integral_normOne
-- name    : GroundTheory.Global.integral_ideleMeasure_eq_integral_normOne
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:25.739128+00:00
-- url     : https://prove2.me/theorems/f5ef1403-f30a-5abd-b462-615bad248fb7
-- title:
--   Global: integral idele Measure eq integral norm One
-- statement:
--   The Global construction uses the integral idele Measure eq integral norm One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean#L384-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean#L384-L402

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem GroundTheory.Global.integral_ideleMeasure_eq_integral_normOne {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (w : InfinitePlace K) {f : IdeleGroup K → E}
    (hf : Integrable f (ideleMeasure K)) :
    ∫ x, f x ∂ideleMeasure K =
      ∫ t, ∫ u, f ((u : IdeleGroup K) * moduleSection w t) ∂normOneMeasure K ∂posRealMeasure := by sorry
