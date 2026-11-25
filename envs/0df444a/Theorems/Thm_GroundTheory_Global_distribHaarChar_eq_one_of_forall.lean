-- Prove2me | Theorems.Thm_GroundTheory_Global_distribHaarChar_eq_one_of_forall
-- name    : GroundTheory.Global.distribHaarChar_eq_one_of_forall
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:10:06.510647+00:00
-- url     : https://prove2.me/theorems/2319d80e-dbbb-4770-885c-ff8ab8734d4d
-- title:
--   Global: distrib Haar Char eq one of forall
-- statement:
--   The Global construction uses the distrib Haar Char eq one of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L140-L145

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

theorem GroundTheory.Global.distribHaarChar_eq_one_of_forall {w : (𝔸ᶠ[K])ˣ} (hw : ∀ v, IsIntegralUnitAt w v) :
    distribHaarChar 𝔸ᶠ[K] w = 1 := by sorry
