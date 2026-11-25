-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_primePowRoots_finite_ncard
-- name    : GlobalTheory.BadShare.primePowRoots_finite_ncard
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:17.865866+00:00
-- url     : https://prove2.me/theorems/1b0f67e2-8b21-4c39-bf09-f84545adcc41
-- title:
--   Bad Share: prime Pow Roots finite ncard
-- statement:
--   The Bad Share construction uses the prime Pow Roots finite ncard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PowPadicValEqOneOfPrimePow.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PowPadicValEqOneOfPrimePow.lean#L19-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.primePowRoots_finite_ncard (k : Type) [Field k] (n l : ℕ) (hn : 0 < n) (hl : l.Prime) :
    {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
      {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n := by sorry
