-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_Test_swap_ne_scalar
-- name    : GlobalTheory.PDivGroup.Test.swap_ne_scalar
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:26.538927+00:00
-- url     : https://prove2.me/theorems/e4b2b74e-a927-5f57-983c-fa3efde8b81e
-- title:
--   Test: swap ne scalar
-- statement:
--   The Test construction uses the swap ne scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L222-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L222-L239

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

theorem GlobalTheory.PDivGroup.Test.swap_ne_scalar [Fact p.Prime] [Nontrivial O] (a : ℤ_[p]) :
    swapAction (const p O) Polynomial.X ≠ padicAction _ a := by sorry
