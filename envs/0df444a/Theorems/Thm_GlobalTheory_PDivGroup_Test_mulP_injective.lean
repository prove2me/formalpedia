-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_Test_mulP_injective
-- name    : GlobalTheory.PDivGroup.Test.mulP_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:27.072866+00:00
-- url     : https://prove2.me/theorems/82dc781b-0294-4645-bad5-6a6b47b307c9
-- title:
--   Test: mul P injective
-- statement:
--   The Test construction uses the mul P injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L68-L75

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
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
variable {p : ℕ} {O : Type} [CommRing O]

theorem GlobalTheory.PDivGroup.Test.mulP_injective (G : _root_.GlobalTheory.PDivGroup p O) (n : ℕ) :
    Function.Injective (G.mulP n) := by sorry
