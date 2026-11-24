-- Prove2me | Theorems.Thm_GlobalTheory_meanSq_card_primeFactors_outPart
-- name    : GlobalTheory.meanSq_card_primeFactors_outPart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:12:00.78083+00:00
-- url     : https://prove2.me/theorems/4ae33e39-1867-4d91-8542-34a72f01a754
-- title:
--   Global Theory: mean Sq card prime Factors out Part
-- statement:
--   The Global Theory construction uses the mean Sq card prime Factors out Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L93-L99

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

theorem GlobalTheory.meanSq_card_primeFactors_outPart (m₀ : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n') :
    (outPart m₀ (n * n')).primeFactors.card ≤ 2 := by sorry
