-- Prove2me | Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_inv
-- name    : GroundTheory.Global.summable_absNorm_rpow_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:15.926816+00:00
-- url     : https://prove2.me/theorems/a628cd14-bc20-4bc8-a295-0bbdf26849c0
-- title:
--   Global: summable abs Norm rpow inv
-- statement:
--   The Global construction uses the summable abs Norm rpow inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L224-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L224-L226

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.summable_absNorm_rpow_inv {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) ↦ ((absNorm I : ℝ) ^ σ)⁻¹ := by sorry
