-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_heightOneSpectrum_dvd
-- name    : GroundTheory.Global.exists_heightOneSpectrum_dvd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:20:02.945084+00:00
-- url     : https://prove2.me/theorems/b56e7015-d0a5-5155-9928-8f37b52ebdac
-- title:
--   Global: exists height One Spectrum dvd
-- statement:
--   The Global construction uses the exists height One Spectrum dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L25-L29

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

theorem GroundTheory.Global.exists_heightOneSpectrum_dvd {I : Ideal R} (h0 : I ≠ ⊥) (h1 : I ≠ ⊤) :
    ∃ v : HeightOneSpectrum R, v.asIdeal ∣ I := by sorry
