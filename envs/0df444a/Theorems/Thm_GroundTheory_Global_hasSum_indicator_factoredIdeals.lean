-- Prove2me | Theorems.Thm_GroundTheory_Global_hasSum_indicator_factoredIdeals
-- name    : GroundTheory.Global.hasSum_indicator_factoredIdeals
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:40.478811+00:00
-- url     : https://prove2.me/theorems/d8076e68-38a2-5333-947b-b5b2ffb8c654
-- title:
--   Global: has Sum indicator factored Ideals
-- statement:
--   The Global construction uses the has Sum indicator factored Ideals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L122-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L122-L171

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

theorem GroundTheory.Global.hasSum_indicator_factoredIdeals (hsum : Summable fun I ↦ ‖g I‖)
    (S : Finset (HeightOneSpectrum R)) :
    HasSum ((factoredIdeals S).indicator g) (∏ v ∈ S, (1 - g v.asIdeal)⁻¹) := by sorry
