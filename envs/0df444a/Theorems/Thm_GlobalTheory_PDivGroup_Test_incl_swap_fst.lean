-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_Test_incl_swap_fst
-- name    : GlobalTheory.PDivGroup.Test.incl_swap_fst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:04.954003+00:00
-- url     : https://prove2.me/theorems/c54bf086-37c9-4f2e-a7b1-1345fed9365e
-- title:
--   Test: incl swap fst
-- statement:
--   The Test construction uses the incl swap fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L212-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L212-L217

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

theorem GlobalTheory.PDivGroup.Test.incl_swap_fst (G : PDivGroup p O) : incl G G ≫ swap G ≫ fst G G = 0 := by sorry
