-- Prove2me | Theorems.Thm_GlobalTheory_meanSq_expand
-- name    : GlobalTheory.meanSq_expand
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:12:03.124492+00:00
-- url     : https://prove2.me/theorems/69ca17d1-65b4-4e96-a8dc-676d6d05c449
-- title:
--   Global Theory: mean Sq expand
-- statement:
--   The Global Theory construction uses the mean Sq expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L42-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L42-L76

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

theorem GlobalTheory.meanSq_expand (I PPs : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ) (hκ : ∀ n, ‖κ n‖ ≤ 1) :
    (∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2) / PPs.card ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' *
        |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| := by sorry
