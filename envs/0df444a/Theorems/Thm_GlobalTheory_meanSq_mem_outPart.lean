-- Prove2me | Theorems.Thm_GlobalTheory_meanSq_mem_outPart
-- name    : GlobalTheory.meanSq_mem_outPart
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:18.781972+00:00
-- url     : https://prove2.me/theorems/c069e697-abbe-4e2c-ab5f-2bbc2e68304d
-- title:
--   Global Theory: mean Sq mem out Part
-- statement:
--   The Global Theory construction uses the mean Sq mem out Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L101-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L101-L114

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

theorem GlobalTheory.meanSq_mem_outPart (m₀ : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (hne : n.minFac ≠ n'.minFac) (hsq : ¬ IsSquare n) (hm : ¬ n.minFac ∣ m₀) :
    n.minFac ∈ (outPart m₀ (n * n')).primeFactors := by sorry
