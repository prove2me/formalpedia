-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_coeffTerm_apply
-- name    : GroundTheory.Global.HeckeCharacter.coeffTerm_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:02:17.876607+00:00
-- url     : https://prove2.me/theorems/07b6d831-3b8a-47f1-be15-c67de2158c21
-- title:
--   Hecke Character: coeff Term apply
-- statement:
--   The Hecke Character construction uses the coeff Term apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L338-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L338-L340

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

theorem GroundTheory.Global.HeckeCharacter.coeffTerm_apply (s : ℂ) (I : Ideal (𝓞 K)) :
    χ.coeffTerm s I = χ.coeff I / (absNorm I : ℂ) ^ s := by sorry
