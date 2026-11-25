-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_hasSum_term_LCoeff
-- name    : GroundTheory.Global.HeckeCharacter.hasSum_term_LCoeff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:21.591534+00:00
-- url     : https://prove2.me/theorems/b901d447-ac65-4415-a223-bb2a0111e2dc
-- title:
--   Hecke Character: has Sum term LCoeff
-- statement:
--   The Hecke Character construction uses the has Sum term LCoeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L366-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L366-L383

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

theorem GroundTheory.Global.HeckeCharacter.hasSum_term_LCoeff {s : ℂ} (hs : 1 < s.re) :
    HasSum (LSeries.term χ.LCoeff s) (∑' I, χ.coeffTerm s I) := by sorry
