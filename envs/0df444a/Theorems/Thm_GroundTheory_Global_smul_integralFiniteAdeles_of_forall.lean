-- Prove2me | Theorems.Thm_GroundTheory_Global_smul_integralFiniteAdeles_of_forall
-- name    : GroundTheory.Global.smul_integralFiniteAdeles_of_forall
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:46.552897+00:00
-- url     : https://prove2.me/theorems/3ba0b35d-ed4c-49c3-8d14-6e4e3253751e
-- title:
--   Global: smul integral Finite Adeles of forall
-- statement:
--   The Global construction uses the smul integral Finite Adeles of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L127-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L127-L138

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

theorem GroundTheory.Global.smul_integralFiniteAdeles_of_forall {w : (𝔸ᶠ[K])ˣ} (hw : ∀ v, IsIntegralUnitAt w v) :
    w • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) = integralFiniteAdeles (𝓞 K) K := by sorry
