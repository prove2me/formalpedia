-- Prove2me | Theorems.Thm_GroundTheory_Global_norm_eq_one_of_isIntegralUnitAt
-- name    : GroundTheory.Global.norm_eq_one_of_isIntegralUnitAt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:36.365381+00:00
-- url     : https://prove2.me/theorems/3aec04ce-e60f-4f8e-ad45-a62a7bc323e3
-- title:
--   Global: norm eq one of is Integral Unit At
-- statement:
--   The Global construction uses the norm eq one of is Integral Unit At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L106-L108

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

theorem GroundTheory.Global.norm_eq_one_of_isIntegralUnitAt {u : (𝔸ᶠ[K])ˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h : IsIntegralUnitAt u v) : ‖(u : 𝔸ᶠ[K]) v‖ = 1 := by sorry
