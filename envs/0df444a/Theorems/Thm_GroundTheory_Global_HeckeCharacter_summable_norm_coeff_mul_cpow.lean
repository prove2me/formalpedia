-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_summable_norm_coeff_mul_cpow
-- name    : GroundTheory.Global.HeckeCharacter.summable_norm_coeff_mul_cpow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:31.542233+00:00
-- url     : https://prove2.me/theorems/520af124-8226-4e16-8b46-c4e8fb9663b2
-- title:
--   Hecke Character: summable norm coeff mul cpow
-- statement:
--   The Hecke Character construction uses the summable norm coeff mul cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L392-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L392-L394

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
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

theorem GroundTheory.Global.HeckeCharacter.summable_norm_coeff_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) ↦ ‖χ.coeff I * (absNorm I : ℂ) ^ (-s)‖ := by sorry
