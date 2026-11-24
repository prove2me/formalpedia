-- Prove2me | Theorems.Thm_GlobalTheory_meanSq_fiber_le
-- name    : GlobalTheory.meanSq_fiber_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:42.472277+00:00
-- url     : https://prove2.me/theorems/c0db4252-4131-4f60-b46e-3b9a8ddd7146
-- title:
--   Global Theory: mean Sq fiber le
-- statement:
--   The Global Theory construction uses the mean Sq fiber le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanSqCardPrimeFactorsOutPart.lean#L21-L40

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

theorem GlobalTheory.meanSq_fiber_le {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (if n.minFac = p then cn x n else 0) ≤ sP x p := by sorry
