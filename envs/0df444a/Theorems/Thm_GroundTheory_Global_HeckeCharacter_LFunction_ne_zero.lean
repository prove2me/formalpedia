-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_LFunction_ne_zero
-- name    : GroundTheory.Global.HeckeCharacter.LFunction_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:55:46.774351+00:00
-- url     : https://prove2.me/theorems/4c0ef232-11a3-527b-9b7f-5f14115c434a
-- title:
--   Hecke Character: LFunction ne zero
-- statement:
--   The Hecke Character construction uses the LFunction ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L466-L493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L466-L493

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

theorem GroundTheory.Global.HeckeCharacter.LFunction_ne_zero {s : ℂ} (hs : 1 < s.re) : χ.LFunction s ≠ 0 := by sorry
