-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_TwoRoots_sum_pow_le
-- name    : GlobalTheory.BadShare.TwoRoots.sum_pow_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:32.423796+00:00
-- url     : https://prove2.me/theorems/27540784-7ae1-471f-897b-1b2e9b212db4
-- title:
--   Two Roots: sum pow le
-- statement:
--   The Two Roots construction uses the sum pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardIrreducibleSamePrimeToPartRootsLe.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardIrreducibleSamePrimeToPartRootsLe.lean#L73-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.TwoRoots

theorem GlobalTheory.BadShare.TwoRoots.sum_pow_le {g : ℕ} (hg : 2 ≤ g) (m : ℕ) : ∑ e ∈ Finset.Icc 1 m, g ^ e ≤ 2 * g ^ m := by sorry
