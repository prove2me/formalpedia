-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_ideleMeasure_eq_integral_fundamentalDomain
-- name    : GroundTheory.Global.integral_ideleMeasure_eq_integral_fundamentalDomain
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:57:04.948111+00:00
-- url     : https://prove2.me/theorems/5204c7b9-cb3a-5fe2-886f-e1e0488a532e
-- title:
--   Global: integral idele Measure eq integral fundamental Domain
-- statement:
--   The Global construction uses the integral idele Measure eq integral fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean#L291-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean#L291-L314

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

theorem GroundTheory.Global.integral_ideleMeasure_eq_integral_fundamentalDomain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (w : InfinitePlace K) {F : IdeleGroup K → E}
    (hF : Integrable F (ideleMeasure K)) :
    ∫ x, F x ∂ideleMeasure K =
      ∫ t, ∫ u in normOneFundamentalDomain K,
        ∑' ξ : Kˣ, F (diagonal K ξ * moduleSection w t * u) ∂normOneMeasure K
        ∂posRealMeasure := by sorry
