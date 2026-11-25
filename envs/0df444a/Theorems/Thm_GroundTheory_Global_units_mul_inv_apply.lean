-- Prove2me | Theorems.Thm_GroundTheory_Global_units_mul_inv_apply
-- name    : GroundTheory.Global.units_mul_inv_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:10:02.852961+00:00
-- url     : https://prove2.me/theorems/bc9cd7d2-2157-4bad-8d4c-ac018e652eee
-- title:
--   Global: units mul inv apply
-- statement:
--   The Global construction uses the units mul inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L102-L104

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

theorem GroundTheory.Global.units_mul_inv_apply (u : (𝔸ᶠ[K])ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (u : 𝔸ᶠ[K]) v * ((u⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v = 1 := by sorry
