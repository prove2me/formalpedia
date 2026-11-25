-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_summable_norm_coeffTerm
-- name    : GroundTheory.Global.HeckeCharacter.summable_norm_coeffTerm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:12:30.232876+00:00
-- url     : https://prove2.me/theorems/0fd3dd1d-0bce-406b-b307-47727f9016a8
-- title:
--   Hecke Character: summable norm coeff Term
-- statement:
--   The Hecke Character construction uses the summable norm coeff Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L356-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L356-L358

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

theorem GroundTheory.Global.HeckeCharacter.summable_norm_coeffTerm {s : ℂ} (hs : 1 < s.re) :
    Summable fun I ↦ ‖χ.coeffTerm s I‖ := by sorry
