-- Prove2me | Theorems.Thm_OAI_LargePrimeGaps_extra_cumulative_pair_limit
-- name    : OAI.LargePrimeGaps.extra_cumulative_pair_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:53:21.402853+00:00
-- url     : https://prove2.me/theorems/96ffbfe8-58b1-4e3d-8c8f-82809367f74a
-- title:
--   OAI.LargePrimeGaps.extra_cumulative_pair_limit: intermediate lemma from OpenAI, Positive lower density of large prime gaps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem344.large_gaps_and_ratio_density`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive lower density of large prime gaps*, OpenAI Math Release, September 25, 2026, result family 26, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LargePrimeGaps.extra_cumulative_pair_limit` of [lean/OAI/NumberTheory/PrimeGaps/DetectorMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/DetectorMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LargePrimeGaps`, with `open Filter`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff`, `open Asymptotics`, `open Asymptotics`, `open Asymptotics`, `open scoped Classical`, `open scoped ContDiff`, `open Topology`, `open scoped Convolution ContDiff Pointwise`):
--
--   ```lean
--   theorem extra_cumulative_pair_limit {n p d : ℕ} {tau sigma lam : ℝ}
--       (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
--       (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
--       (hf : HasCompactSupport f) (hg : HasCompactSupport g)
--       (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
--       (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
--       (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
--       (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
--       Tendsto (fun X : ℕ => (extraAverage X (blockLength lam X) (fun m =>
--         weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
--         weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m)
--         (cumulativeProfile sigma w):ℂ)) atTop
--         (𝓝 ((lam:ℂ)^(d+1)*∑ r : Setoid (Fin (n+p)),
--           (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
--           ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.LargePrimeGaps.blockLength`, `OAI.LargePrimeGaps.cumulativeProfile`, `OAI.LargePrimeGaps.extraAverage`, `OAI.LargePrimeGaps.extraPairKernel`, `OAI.LargePrimeGaps.finiteSetoidFintype`, `OAI.LargePrimeGaps.positiveSimplex`, `OAI.LargePrimeGaps.subsetCoefficient`, `OAI.LargePrimeGaps.tensorCoefficient` and `OAI.LargePrimeGaps.weightedBlock` (definitions bundle `OAIW2PG000` of this split).
--
--   **Used by.** The proof of `OAI.LargePrimeGaps.unorderedWeight_detector_bound` of this split imports it.
-- source:
--   OpenAI, Positive lower density of large prime gaps, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 26; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/DetectorMoments.lean (declaration OAI.LargePrimeGaps.extra_cumulative_pair_limit)

import Mathlib
import Definitions.Def_OAIW2PG000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem extra_cumulative_pair_limit {n p d : ℕ} {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => (extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m)
      (cumulativeProfile sigma w):ℂ)) atTop
      (𝓝 ((lam:ℂ)^(d+1)*∑ r : Setoid (Fin (n+p)),
        (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r))) := by
  sorry

end LargePrimeGaps

end OAI
end
