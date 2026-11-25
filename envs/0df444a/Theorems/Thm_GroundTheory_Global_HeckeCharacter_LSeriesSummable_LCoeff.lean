-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_LSeriesSummable_LCoeff
-- name    : GroundTheory.Global.HeckeCharacter.LSeriesSummable_LCoeff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:12:49.657323+00:00
-- url     : https://prove2.me/theorems/c5199968-4ff7-40ee-8a26-67973daab850
-- title:
--   Hecke Character: LSeries Summable LCoeff
-- statement:
--   The Hecke Character construction uses the LSeries Summable LCoeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L385-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L385-L386

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

theorem GroundTheory.Global.HeckeCharacter.LSeriesSummable_LCoeff {s : ℂ} (hs : 1 < s.re) : LSeriesSummable χ.LCoeff s := by sorry
