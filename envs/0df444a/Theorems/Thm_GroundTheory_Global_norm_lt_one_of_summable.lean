-- Prove2me | Theorems.Thm_GroundTheory_Global_norm_lt_one_of_summable
-- name    : GroundTheory.Global.norm_lt_one_of_summable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:52.165607+00:00
-- url     : https://prove2.me/theorems/25a63a79-f4a3-4d44-a512-0becacf5d4cc
-- title:
--   Global: norm lt one of summable
-- statement:
--   The Global construction uses the norm lt one of summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L113-L120

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
variable {R : Type*} [CommRing R] [IsDedekindDomain R] (g : Ideal R →* ℂ)

theorem GroundTheory.Global.norm_lt_one_of_summable (hsum : Summable fun I ↦ ‖g I‖) (v : HeightOneSpectrum R) :
    ‖g v.asIdeal‖ < 1 := by sorry
