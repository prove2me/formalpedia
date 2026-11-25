-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_Test_tate_torsionFree
-- name    : GlobalTheory.PDivGroup.Test.tate_torsionFree
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:47.376298+00:00
-- url     : https://prove2.me/theorems/ebe92ab0-1f3a-500f-9837-4e547f328c10
-- title:
--   Test: tate torsion Free
-- statement:
--   The Test construction uses the tate torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L99-L109

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

theorem GlobalTheory.PDivGroup.Test.tate_torsionFree [Fact p.Prime] (G : PDivGroup p O) {B : Type} [CommRing B] [Algebra O B]
    (x : G.TateOver B) (h : (p : ℤ_[p]) • x = 0) : x = 0 := by sorry
