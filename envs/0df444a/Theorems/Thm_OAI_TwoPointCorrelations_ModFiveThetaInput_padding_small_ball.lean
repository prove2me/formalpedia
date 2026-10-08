-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_padding_small_ball
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.padding_small_ball
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:53.733336+00:00
-- url     : https://prove2.me/theorems/87c42919-d048-47c1-95db-1bf1babbff44
-- title:
--   Under the mod-5 prime number theorem, the padding difference is rarely within 1 of zero
-- statement:
--   Assume `ModFiveThetaInput`. Let $E$ be a finite set of naturals. Then there is $C>0$ such that for every $L\ge1$,
--
--   $$\Pr\Big(\big|\texttt{paddingDifferenceValue}(Q,x)\big|\le1\Big)\le\frac CL,$$
--
--   where $Q$ = `paddingPrimeSupply E L` (the primes $p\le e^L$ with $p\not\equiv1\pmod5$, minus $E$) and the probability is under the bundle's padding difference law `paddingDifferenceLaw Q` on that supply.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.padding_small_ball`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem ModFiveThetaInput.padding_small_ball (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (paddingDifferenceLaw (paddingPrimeSupply E L)
        (fun _ hp => (paddingPrimeSupply_prime hp).two_le)).probability
          (fun x => |paddingDifferenceValue (paddingPrimeSupply E L) x| ≤ 1) ≤ C / L := by
  sorry

end OAI.TwoPointCorrelations
