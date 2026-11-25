-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_constFun_res
-- name    : GlobalTheory.PDivGroup.constFun_res
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:14.535787+00:00
-- url     : https://prove2.me/theorems/fbbd88e9-15b2-595b-8944-c78a930bbca1
-- title:
--   PDiv Group: const Fun res
-- statement:
--   The PDiv Group construction uses the const Fun res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L734-L738
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L734-L738

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
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
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable (p O) [Fact p.Prime]

theorem GlobalTheory.PDivGroup.constFun_res (n : ℕ) (φ : (const p O).A (n + 1)) (k : ℕ) :
    constFun p O n ((const p O).res n φ) k = constFun p O (n + 1) φ (p * k : ℕ) := by sorry
