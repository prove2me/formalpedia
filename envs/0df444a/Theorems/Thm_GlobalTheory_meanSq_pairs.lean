-- Prove2me | Theorems.Thm_GlobalTheory_meanSq_pairs
-- name    : GlobalTheory.meanSq_pairs
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:24.878922+00:00
-- url     : https://prove2.me/theorems/fb9c4292-be9b-4a7e-b3f3-77fd9e02f972
-- title:
--   Global Theory: mean Sq pairs
-- statement:
--   The Global Theory construction uses the mean Sq pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L116-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L116-L234

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MeanSqCardPrimeFactorsOutPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

theorem GlobalTheory.meanSq_pairs {x : ℝ} (hx : 0 ≤ x) (m₀ : ℕ) (hm₀ : 0 < m₀) (nStar : ℕ) (A : ℕ → ℕ → ℝ) (η S : ℝ)
    (hη : 0 ≤ η) (hS0 : 0 ≤ S) (hS : ∀ p : ℕ, p.Prime → sP x p ≤ S) (hA1 : ∀ n n', A n n' ≤ 1)
    (hA : ∀ n n' : ℕ, n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ → n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ →
      IsPrimePow n → IsPrimePow n' → outPart m₀ (n * n') ≠ 1 → outPart m₀ (n * n') ≠ nStar → A n n' ≤ η) :
    ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, ∑ n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n * cn x n' * A n n' ≤
      η * (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 +
      ∑ p ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun p => p.Prime), sP x p ^ 2 +
      (Rsum x m₀ + 2 * S) ^ 2 := by sorry
