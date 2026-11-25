-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_prod_finiteSingleUnits_apply
-- name    : GroundTheory.Global.coe_prod_finiteSingleUnits_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:10:32.285894+00:00
-- url     : https://prove2.me/theorems/b9a6df91-a277-489b-a40a-ccb8deeb85f8
-- title:
--   Global: coe prod finite Single Units apply
-- statement:
--   The Global construction uses the coe prod finite Single Units apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L79-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L79-L92

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
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
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open scoped Classical

theorem GroundTheory.Global.coe_prod_finiteSingleUnits_apply (T : Finset (HeightOneSpectrum (𝓞 K)))
    (f : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (x : HeightOneSpectrum (𝓞 K)) :
    ((∏ v ∈ T, finiteSingleUnits v (f v) : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x =
      if x ∈ T then ((f x : (x.adicCompletion K)ˣ) : x.adicCompletion K) else 1 := by sorry
