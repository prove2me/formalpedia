-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_coeff_asIdeal_of_not_dvd
-- name    : GroundTheory.Global.HeckeCharacter.coeff_asIdeal_of_not_dvd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:03.246513+00:00
-- url     : https://prove2.me/theorems/9ef4bd30-d939-5a77-a068-a8d61c6992f0
-- title:
--   Hecke Character: coeff as Ideal of not dvd
-- statement:
--   The Hecke Character construction uses the coeff as Ideal of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L325-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L325-L329

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

theorem GroundTheory.Global.HeckeCharacter.coeff_asIdeal_of_not_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor) :
    χ.coeff v.asIdeal =
      χ.idealCharacter ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ := by sorry
