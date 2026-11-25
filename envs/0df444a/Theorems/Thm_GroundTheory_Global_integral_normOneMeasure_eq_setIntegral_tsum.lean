-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_normOneMeasure_eq_setIntegral_tsum
-- name    : GroundTheory.Global.integral_normOneMeasure_eq_setIntegral_tsum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:37:18.051701+00:00
-- url     : https://prove2.me/theorems/ce2f3050-60cd-4026-8e2f-1cfd866d94e0
-- title:
--   Global: integral norm One Measure eq set Integral tsum
-- statement:
--   The Global construction uses the integral norm One Measure eq set Integral tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean#L265-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean#L265-L289

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureQuotient
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
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.integral_normOneMeasure_eq_setIntegral_tsum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : normOneSubgroup K → E} (hf : Integrable f (normOneMeasure K)) :
    ∫ u, f u ∂normOneMeasure K = ∫ u in normOneFundamentalDomain K,
      ∑' ξ : Kˣ, f (diagonalToNormOne K ξ * u) ∂normOneMeasure K := by sorry
