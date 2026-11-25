-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_LFunction_hasProd_all
-- name    : GroundTheory.Global.HeckeCharacter.LFunction_hasProd_all
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:12:46.21699+00:00
-- url     : https://prove2.me/theorems/61bb64bb-f4ed-4f82-9ace-210064cf68d6
-- title:
--   Hecke Character: LFunction has Prod all
-- statement:
--   The Hecke Character construction uses the LFunction has Prod all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L435-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L435-L441

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

theorem GroundTheory.Global.HeckeCharacter.LFunction_hasProd_all {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) ↦
      (1 - χ.coeff v.asIdeal * (absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s) := by sorry
