-- Prove2me | Theorems.Thm_GroundTheory_Global_distribHaarChar_finiteSingleUnits_uniformizer
-- name    : GroundTheory.Global.distribHaarChar_finiteSingleUnits_uniformizer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:03.129302+00:00
-- url     : https://prove2.me/theorems/dc3d2459-468f-45c6-85d8-cd3452660314
-- title:
--   Global: distrib Haar Char finite Single Units uniformizer
-- statement:
--   The Global construction uses the distrib Haar Char finite Single Units uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L246-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L246-L264

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

theorem GroundTheory.Global.distribHaarChar_finiteSingleUnits_uniformizer {v : HeightOneSpectrum (𝓞 K)}
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (hϖ0 : (ϖ : v.adicCompletion K) ≠ 0) :
    distribHaarChar 𝔸ᶠ[K] (finiteSingleUnits v (Units.mk0 _ hϖ0)) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by sorry
