-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_Test_height_eq_of_iso
-- name    : GlobalTheory.PDivGroup.Test.height_eq_of_iso
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:43.768636+00:00
-- url     : https://prove2.me/theorems/553c4287-29df-4ea7-91f1-82002480529c
-- title:
--   Test: height eq of iso
-- statement:
--   The Test construction uses the height eq of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L28-L40

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

theorem GlobalTheory.PDivGroup.Test.height_eq_of_iso [Fact p.Prime] [Nontrivial O] {G H : PDivGroup p O} (e : G ≅ H) :
    G.height = H.height := by sorry
