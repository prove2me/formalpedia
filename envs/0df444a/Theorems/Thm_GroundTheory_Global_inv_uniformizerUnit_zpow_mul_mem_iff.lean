-- Prove2me | Theorems.Thm_GroundTheory_Global_inv_uniformizerUnit_zpow_mul_mem_iff
-- name    : GroundTheory.Global.inv_uniformizerUnit_zpow_mul_mem_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:59.69095+00:00
-- url     : https://prove2.me/theorems/cbd4a96c-0128-4c00-8df2-192fea626363
-- title:
--   Global: inv uniformizer Unit zpow mul mem iff
-- statement:
--   The Global construction uses the inv uniformizer Unit zpow mul mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L53-L58

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.inv_uniformizerUnit_zpow_mul_mem_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℤ)
    (y : v.adicCompletion K) :
    ((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ * y ∈
        v.adicCompletionIntegers K ↔ Valued.v y ≤ exp (-n) := by sorry
