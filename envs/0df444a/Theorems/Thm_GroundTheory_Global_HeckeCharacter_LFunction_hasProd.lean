-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_LFunction_hasProd
-- name    : GroundTheory.Global.HeckeCharacter.LFunction_hasProd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:08.806026+00:00
-- url     : https://prove2.me/theorems/61b56440-5260-5c49-95cf-440be3b35367
-- title:
--   Hecke Character: LFunction has Prod
-- statement:
--   The Hecke Character construction uses the LFunction has Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L443-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L443-L464

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

theorem GroundTheory.Global.HeckeCharacter.LFunction_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
      (1 - (χ.idealCharacter ⟨primeIdealUnit v.1, primeIdealUnit_mem_idealsPrimeTo v.2⟩ : ℂ) *
        (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s) := by sorry
