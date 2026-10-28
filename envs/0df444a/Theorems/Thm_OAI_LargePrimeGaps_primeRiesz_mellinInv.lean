-- Prove2me | Theorems.Thm_OAI_LargePrimeGaps_primeRiesz_mellinInv
-- name    : OAI.LargePrimeGaps.primeRiesz_mellinInv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:53:09.839954+00:00
-- url     : https://prove2.me/theorems/e4e23dea-f808-405b-8181-53c4b4f628af
-- title:
--   OAI.LargePrimeGaps.primeRiesz_mellinInv: intermediate lemma from OpenAI, Positive lower density of large prime gaps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem344.large_gaps_and_ratio_density`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive lower density of large prime gaps*, OpenAI Math Release, September 25, 2026, result family 26, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LargePrimeGaps.primeRiesz_mellinInv` of [lean/OAI/NumberTheory/PrimeGaps/RieszDecay.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/RieszDecay.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LargePrimeGaps`, with `open Complex Real Set MeasureTheory Filter Topology`, `open Complex Filter Topology`, `open Complex Filter Topology MeasureTheory`, `open scoped FourierTransform`, `open Complex Real Set MeasureTheory Filter Topology`, `open Complex Real Set MeasureTheory Filter Topology`, `open Complex Real Set MeasureTheory Filter Topology`, `open scoped FourierTransform`, `open Complex Real Set MeasureTheory Filter Topology`):
--
--   ```lean
--   lemma primeRiesz_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
--       (hp : χ.IsPrimitive) {σ x : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hx : 0<x) :
--       mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)=
--         rieszSum (primeCoefficients χ) x-characterMain χ*poleRieszKernel (1/x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LargePrimeGaps.characterMain`, `OAI.LargePrimeGaps.logRiesz`, `OAI.LargePrimeGaps.poleRemovedL`, `OAI.LargePrimeGaps.poleRieszKernel`, `OAI.LargePrimeGaps.primeCoefficients` and `OAI.LargePrimeGaps.rieszSum` (definitions bundle `OAIW2PG000` of this split).
--
--   **Used by.** The proof of `OAI.LargePrimeGaps.primeWeighted_error_bound` of this split imports it.
-- source:
--   OpenAI, Positive lower density of large prime gaps, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 26; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/RieszDecay.lean (declaration OAI.LargePrimeGaps.primeRiesz_mellinInv)

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

lemma primeRiesz_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ x : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hx : 0<x) :
    mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)=
      rieszSum (primeCoefficients χ) x-characterMain χ*poleRieszKernel (1/x) := by
  sorry

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

end LargePrimeGaps

end OAI
end
