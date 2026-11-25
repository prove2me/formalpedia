-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_coeff_asIdeal_of_dvd
-- name    : GroundTheory.Global.HeckeCharacter.coeff_asIdeal_of_dvd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:02.73464+00:00
-- url     : https://prove2.me/theorems/67006f73-104d-50ec-af14-bd29e8a11c0d
-- title:
--   Hecke Character: coeff as Ideal of dvd
-- statement:
--   The Hecke Character construction uses the coeff as Ideal of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L321-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L321-L323

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

theorem GroundTheory.Global.HeckeCharacter.coeff_asIdeal_of_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.conductor) :
    χ.coeff v.asIdeal = 0 := by sorry
