-- Prove2me | Theorems.Thm_GroundTheory_Global_heightOneSpectrum_eq_of_dvd
-- name    : GroundTheory.Global.heightOneSpectrum_eq_of_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:03:42.351622+00:00
-- url     : https://prove2.me/theorems/6d504aac-b7ec-47db-9b13-7f0ee57a593b
-- title:
--   Global: height One Spectrum eq of dvd
-- statement:
--   The Global construction uses the height One Spectrum eq of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L16-L19

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
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem GroundTheory.Global.heightOneSpectrum_eq_of_dvd {v w : HeightOneSpectrum R} (h : w.asIdeal ∣ v.asIdeal) :
    w = v := by sorry
