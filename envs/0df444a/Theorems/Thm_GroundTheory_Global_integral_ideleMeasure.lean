-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_ideleMeasure
-- name    : GroundTheory.Global.integral_ideleMeasure
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:22.418799+00:00
-- url     : https://prove2.me/theorems/c9d1fb87-c0f5-560e-8f6a-6630ead1d176
-- title:
--   Global: integral idele Measure
-- statement:
--   The Global construction uses the integral idele Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L478-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L478-L482

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
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
open scoped NumberField.AdeleRing RestrictedProduct ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.integral_ideleMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : IdeleGroup K → E) :
    ∫ x, f x ∂ideleMeasure K = ∫ p, f ((IdeleGroup.prodEquiv K).symm p)
      ∂(infiniteIdeleMeasure K).prod (finiteIdeleMeasure K) := by sorry
