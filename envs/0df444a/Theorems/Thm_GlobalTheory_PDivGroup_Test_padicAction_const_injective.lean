-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_Test_padicAction_const_injective
-- name    : GlobalTheory.PDivGroup.Test.padicAction_const_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:33.504876+00:00
-- url     : https://prove2.me/theorems/400ae73d-0abe-41de-9031-a6a9953506f3
-- title:
--   Test: padic Action const injective
-- statement:
--   The Test construction uses the padic Action const injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L49-L59

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

theorem GlobalTheory.PDivGroup.Test.padicAction_const_injective [Fact p.Prime] [Nontrivial O] :
    Function.Injective (padicAction (const p O)) := by sorry
