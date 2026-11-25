-- Prove2me | Theorems.Thm_GroundTheory_Global_heightOneSpectrum_eq_of_dvd_pow
-- name    : GroundTheory.Global.heightOneSpectrum_eq_of_dvd_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:43.325681+00:00
-- url     : https://prove2.me/theorems/12082224-7b8b-41b0-b995-506643e7173d
-- title:
--   Global: height One Spectrum eq of dvd pow
-- statement:
--   The Global construction uses the height One Spectrum eq of dvd pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L21-L23

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

theorem GroundTheory.Global.heightOneSpectrum_eq_of_dvd_pow {v w : HeightOneSpectrum R} {k : ℕ}
    (h : w.asIdeal ∣ v.asIdeal ^ k) : w = v := by sorry
