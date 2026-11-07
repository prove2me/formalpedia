-- Prove2me | Theorems.Thm_GaussPart_lemma_3_5_finder
-- name    : GaussPart.lemma_3_5_finder
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:51.468354+00:00
-- url     : https://prove2.me/theorems/7db6ad1e-8bba-425b-afe7-6159c0244659
-- title:
--   Lemma 3.5 — the threshold-finding algorithm (algorithm part; contains the existence part with the same constants)
-- statement:
--   With the constants $C_0,C>1$ of Lemma 3.5 (whose existence part is restated as a conjunct): for every $\delta\in(0,1)$ there is an algorithm that, given samples from $Q$, draws
--   $$O\Big(\frac{(C\Lambda)^k}{\Delta^2}\log\frac2\delta\Big)$$
--   samples, runs in time polynomial in that sample count, and, whenever the hypotheses of Lemma 3.5 hold (in particular some $i\in[k]$ has $|\mathbb E_P[z^i]-\mathbb E_Q[z^i]|\ge\Delta$), with probability at least $1-\delta$ outputs a threshold $\hat t$ such that for every $b\ge C_0\sqrt\Lambda$: $\hat t\in[-b,b]$, $|\Pr_P[z\ge\hat t]-\Pr_Q[z\ge\hat t]|\ge\Delta/(4b^k)$, and $\hat t$ is a $\Delta^2/(C\Lambda)^k$-Gaussian good split.
--
--   Algorithm 1 uses this search, with fresh samples of $Q\mid R$ projected on the finder's direction, to validate each split.
--
--   **Formalization Note** The algorithm is one arithmetic-only program of the sampling real RAM in dimension $1$, chosen with a constant $C'$ before $k,q,\sigma,\Delta,\delta,Q$; it reads $(k,q,\sigma,\Delta,\delta)$ and samples $z\sim Q$ as points of $\mathbb R^1$. The output is register $r_0$. Sample count at most $n_{\max}=C'(C\Lambda)^k/\Delta^2\cdot\log(2/\delta)$ and work at most $C'n_{\max}^{C'}$ on every sample stream.
--
--   Differences from the source:
--   - reading: "there is an algorithm" with costs in arithmetic operations and time → one program of the published sampling real RAM restricted by ArithmeticOnly (exact +, −, ×, ÷, rational literals, comparisons, memory, sample, halt; no √, exp, cos, sin, coins), chosen before all parameters and Q, reaching Q only through sample; reason: the paper names no machine and counts "arithmetic operations" (p.35); the literal list is the non-weaker reading (an extra primitive would weaken the theorem)
--   - encoding: O(((CΛ)^k/Δ²) log(2/δ)) samples, sample-polynomial time → at most n_max = C'(CΛ)^k/Δ² · log(2/δ) samples and work at most C'·n_max^{C'}, one constant C' chosen with the program; reason: the O(·) constant and the polynomial are uniform over all parameters
--   - reading: draws at most … samples, runs in time … → the sample and work bounds hold on every sample stream, and every run halts; reason: worst-case reading of the budgets, the stronger one; Algorithm 1's budgets are fixed
--   - encoding: outputs a threshold satisfying these conclusions → for every b ≥ C₀√Λ the output lies in [−b, b], has tail gap ≥ Δ/(4b^k) and is a Δ²/(CΛ)^k-Gaussian good split, under the lemma's discrepancy hypothesis; reason: "these conclusions" are the existence part's, for the same constants
--   - encoding: the existence part (stated before "Moreover") → restated as the conjunct GoodSplitConstants C₀ C; reason: so the algorithm uses the same constants C₀, C
--   - encoding: with probability at least p → a measurable set of sample streams of i.i.d.-product measure at least p on which every halted state has the property; reason: outer probability of a non-measurable event would be weaker
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Lemma 3.5, p.16 (PDF p.18), last sentence; proof p.18 (PDF p.20)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_hellingerSq

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Lemma 3.5**, algorithm part (with the existence part for the same constants).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Lemma 3.5, p.16 (PDF p.18):

"Moreover, for every δ ∈ (0, 1), there is an algorithm that draws O(((CΛ)^k/∆²) log(2/δ)) =
polylog_{q,k,∆}(2/σ) log(2/δ) samples from Q, runs in sample-polynomial time, and outputs a threshold
satisfying these conclusions with probability at least 1 − δ."

**Formalization Note.**
* The constants `C₀, C` are those of the existence part, which is restated here as the conjunct
  `GoodSplitConstants C₀ C`, so this item contains `GaussPart.lemma_3_5`.
* The algorithm is one `ArithmeticOnly` program of the `GaussMixHH` machine in dimension `1`, chosen
  with a constant `C'` before `k, q, σ, ∆, δ, Q`. It reads `k, q, σ, ∆, δ` (`splitInput`), draws the
  samples `lineEmbed z` with `z ∼ Q` through `sample`, and outputs the threshold in `r[0]`.
* "O(((CΛ)^k/∆²) log(2/δ)) samples": at most `C' (CΛ)^k/∆² · log(2/δ)` on every sample stream.
  "Sample-polynomial time": work at most `C'` times that sample bound to the power `C'`.
* "These conclusions" are those of the existence part under its hypotheses (the moment
  discrepancy): for every `b ≥ C₀√Λ` the output lies in `[−b, b]`, has tail gap at least `∆/(4b^k)`,
  and is a `κ`-Gaussian good split. They hold on a measurable set of streams of measure `≥ 1 − δ`. -/
theorem lemma_3_5_finder :
    ∃ C₀ C : ℝ, 1 < C₀ ∧ 1 < C ∧ GoodSplitConstants C₀ C ∧
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P) (C' : ℝ),
      0 < C' ∧
      ∀ (k : ℕ) (q σ Δ δ : ℝ), 1 ≤ k → 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < Δ → Δ < 1 → 0 < δ → δ < 1 →
      ∀ (Q : Measure ℝ) [IsProbabilityMeasure Q], IsSmooth (gaussianReal 0 1) Q q σ →
        (∀ xs : ℕ → Vec 1, ∃ t : ℕ,
          (GaussMixHH.run P 1 (GaussMixHH.initState 1 (splitInput k q σ Δ δ)) (noCoins, xs) t).halted
              = true ∧
          ((GaussMixHH.run P 1 (GaussMixHH.initState 1 (splitInput k q σ Δ δ)) (noCoins, xs)
              t).samplesUsed : ℝ) ≤
            C' * (C * goodSplitLambda k q σ Δ) ^ k / Δ ^ 2 * Real.log (2 / δ) ∧
          ((GaussMixHH.run P 1 (GaussMixHH.initState 1 (splitInput k q σ Δ δ)) (noCoins, xs)
              t).work : ℝ) ≤
            C' * (C' * (C * goodSplitLambda k q σ Δ) ^ k / Δ ^ 2 * Real.log (2 / δ)) ^ C') ∧
        ((∃ i : ℕ, 1 ≤ i ∧ i ≤ k ∧ Δ ≤ |∫ z, z ^ i ∂(gaussianReal 0 1) - ∫ z, z ^ i ∂Q|) →
          ∃ E : Set (ℕ → Vec 1), MeasurableSet E ∧
            ENNReal.ofReal (1 - δ) ≤ Measure.infinitePi (fun _ : ℕ => Q.map lineEmbed) E ∧
            ∀ xs ∈ E, ∀ t : ℕ,
              (GaussMixHH.run P 1 (GaussMixHH.initState 1 (splitInput k q σ Δ δ)) (noCoins, xs)
                t).halted = true →
              ∀ b : ℝ, C₀ * Real.sqrt (goodSplitLambda k q σ Δ) ≤ b →
                GaussMixHH.output (GaussMixHH.run P 1 (GaussMixHH.initState 1 (splitInput k q σ Δ δ))
                    (noCoins, xs) t) ∈ Set.Icc (-b) b ∧
                Δ / (4 * b ^ k) ≤ |gaussianTail (GaussMixHH.output (GaussMixHH.run P 1
                    (GaussMixHH.initState 1 (splitInput k q σ Δ δ)) (noCoins, xs) t)) -
                  upperTail Q (GaussMixHH.output (GaussMixHH.run P 1
                    (GaussMixHH.initState 1 (splitInput k q σ Δ δ)) (noCoins, xs) t))| ∧
                IsGoodSplit Q (Δ ^ 2 / (C * goodSplitLambda k q σ Δ) ^ k)
                  (GaussMixHH.output (GaussMixHH.run P 1
                    (GaussMixHH.initState 1 (splitInput k q σ Δ δ)) (noCoins, xs) t))) := by sorry

end GaussPart
