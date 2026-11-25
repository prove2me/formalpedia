-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_hasSum_LFunction_coprime
-- name    : GroundTheory.Global.HeckeCharacter.hasSum_LFunction_coprime
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:51.057169+00:00
-- url     : https://prove2.me/theorems/c5c1ec90-aa1d-5d86-a44d-76005f900592
-- title:
--   Hecke Character: has Sum LFunction coprime
-- statement:
--   The Hecke Character construction uses the has Sum LFunction coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L403-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L403-L421

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

theorem GroundTheory.Global.HeckeCharacter.hasSum_LFunction_coprime {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
      (χ.idealCharacter ⟨idealUnit I.1 I.2.1, idealUnit_mem_idealsPrimeTo I.2.1 I.2.2⟩ : ℂ) *
        (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) (χ.LFunction s) := by sorry
