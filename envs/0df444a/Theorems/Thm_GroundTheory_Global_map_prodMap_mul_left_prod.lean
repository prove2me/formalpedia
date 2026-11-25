-- Prove2me | Theorems.Thm_GroundTheory_Global_map_prodMap_mul_left_prod
-- name    : GroundTheory.Global.map_prodMap_mul_left_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:32.33477+00:00
-- url     : https://prove2.me/theorems/48d8c370-292d-5081-8c4c-2a8cc523b7d3
-- title:
--   Global: map prod Map mul left prod
-- statement:
--   The Global construction uses the map prod Map mul left prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L120-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L120-L128

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
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
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.map_prodMap_mul_left_prod (b : (InfiniteAdeleRing K)ˣ) (c : (𝔸ᶠ[K])ˣ) :
    ((infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)).map
      (Prod.map (fun y ↦ (b : InfiniteAdeleRing K) * y) (fun y ↦ (c : 𝔸ᶠ[K]) * y)) =
      (ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ *
        ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((c⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ≥0∞)) •
        (infiniteAdeleMeasure K).prod (finiteAdeleMeasure K) := by sorry
