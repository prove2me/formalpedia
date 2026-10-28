-- Prove2me | Theorems.Thm_OAI_LargePrimeGaps_primeWeighted_error_bound
-- name    : OAI.LargePrimeGaps.primeWeighted_error_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:54:06.04755+00:00
-- url     : https://prove2.me/theorems/a8567de8-94f3-4485-bbf0-feed10af272b
-- title:
--   OAI.LargePrimeGaps.primeWeighted_error_bound: intermediate lemma from OpenAI, Positive lower density of large prime gaps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem344.large_gaps_and_ratio_density`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive lower density of large prime gaps*, OpenAI Math Release, September 25, 2026, result family 26, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LargePrimeGaps.primeWeighted_error_bound` of [lean/OAI/NumberTheory/PrimeGaps/RieszDecay.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/RieszDecay.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LargePrimeGaps`, with `open Complex Real Set MeasureTheory Filter Topology`, `open Complex Filter Topology`, `open Complex Filter Topology MeasureTheory`, `open scoped FourierTransform`, `open Complex Real Set MeasureTheory Filter Topology`, `open Complex Real Set MeasureTheory Filter Topology`, `open Complex Real Set MeasureTheory Filter Topology`, `open scoped FourierTransform`, `open Complex Real Set MeasureTheory Filter Topology`, `open Complex Real Set MeasureTheory Filter Topology`, `open Complex Real Set MeasureTheory Filter Topology`):
--
--   ```lean
--   lemma primeWeighted_error_bound (a : ℝ) :
--       ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
--         ∀ x : ℝ, 1<x → 1≤Real.log x →
--           ‖weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2‖ ≤
--             D*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-a)+x
--   ```
--
--   **Definitions.** The statement is written with `OAI.LargePrimeGaps.characterMain`, `OAI.LargePrimeGaps.primeCoefficients` and `OAI.LargePrimeGaps.weightedPrefix` (definitions bundle `OAIW2PG000` of this split).
--
--   **Used by.** The proof of `OAI.LargePrimeGaps.bombieriVinogradov` of this split imports it.
-- source:
--   OpenAI, Positive lower density of large prime gaps, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 26; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/RieszDecay.lean (declaration OAI.LargePrimeGaps.primeWeighted_error_bound)

import Mathlib
import Definitions.Def_OAIW2PG000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

open Complex Filter Topology

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

lemma primeWeighted_error_bound (a : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 1<x → 1≤Real.log x →
        ‖weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-a)+x := by
  sorry

end LargePrimeGaps

end OAI
end
