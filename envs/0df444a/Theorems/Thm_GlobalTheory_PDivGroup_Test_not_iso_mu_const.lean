-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_Test_not_iso_mu_const
-- name    : GlobalTheory.PDivGroup.Test.not_iso_mu_const
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:46.450804+00:00
-- url     : https://prove2.me/theorems/084191ef-d6d5-5755-9936-c18865978fb1
-- title:
--   Test: not iso mu const
-- statement:
--   The Test construction uses the not iso mu const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean#L42-L47

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

theorem GlobalTheory.PDivGroup.Test.not_iso_mu_const [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    IsEmpty (mu p O ≅ const p O) := by sorry
