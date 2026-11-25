-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_Test_omega_eq_zero_of_isUnit
-- name    : GlobalTheory.PDivGroup.Test.omega_eq_zero_of_isUnit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:14.984768+00:00
-- url     : https://prove2.me/theorems/26907755-c424-4b58-be2c-a90e20d883a0
-- title:
--   Test: omega eq zero of is Unit
-- statement:
--   The Test construction uses the omega eq zero of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L84-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]

theorem GlobalTheory.PDivGroup.Test.omega_eq_zero_of_isUnit (G : PDivGroup p O) (hp : IsUnit (p : O)) (w : G.omega) :
    w = 0 := by sorry
