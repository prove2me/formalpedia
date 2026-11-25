-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_not_two_primes
-- name    : GlobalTheory.BadShare.not_two_primes
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:48.145638+00:00
-- url     : https://prove2.me/theorems/e2d33678-821c-4da8-9481-01239f55c3c4
-- title:
--   Bad Share: not two primes
-- statement:
--   The Bad Share construction uses the not two primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L353-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L353-L357

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
attribute [local instance] GlobalTheory.BadShare.factPrimeThree

theorem GlobalTheory.BadShare.not_two_primes {l a n p : ℕ} (hl : l.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 ∣ n) (h3 : p ∣ n) : ¬ n ∣ l ^ a := by sorry
