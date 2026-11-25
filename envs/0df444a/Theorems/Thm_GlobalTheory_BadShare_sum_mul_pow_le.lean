-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_sum_mul_pow_le
-- name    : GlobalTheory.BadShare.sum_mul_pow_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:49.718504+00:00
-- url     : https://prove2.me/theorems/f2408fd6-7c7d-5bd0-8000-b729f5babff9
-- title:
--   Bad Share: sum mul pow le
-- statement:
--   The Bad Share construction uses the sum mul pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusMassSamePartOneFactorLe.lean#L84-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusMassSamePartOneFactorLe.lean#L84-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassSamePartOneFactorLe
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

theorem GlobalTheory.BadShare.sum_mul_pow_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 8) (N : ℕ) :
    ∑ d ∈ Finset.Icc 2 N, (d : ℝ) * u ^ d ≤ 6 * u ^ 2 := by sorry
