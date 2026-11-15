-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_Supplement_theorem_7_3
-- name    : OnlineRealSampling.Exact.Supplement.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:40:08.51522+00:00
-- url     : https://prove2.me/theorems/bbb672a8-2213-4cd6-b064-b710019e1e43
-- title:
--   Theorem 7.3 — Expected overall-space lower bound
-- statement:
--   There is a constant c>0 independent of the sampler, word size, environment and horizon with the following property. Let S be any exact online oracle sampler, and let the targets be chosen by any published admissible causal environment, using independent external randomness and the preceding public outputs. For every n≥1, if S_n is peak represented storage during the first n rounds, then
--
--   $$\mathbb E[S_n]\ge c\left(\operatorname{slog}(n)+\mathbb E\left[\max_{1\le i\le n}\operatorname{slog}(X_i)\right]\right).$$
--
--   Here slog(x)=ln(max(x,e)). Overall space includes precision-k answer buffers of k bits (the paper's Section 3 charge) and binary output buffers. Both expectations are extended nonnegative expectations, so neither a finite logarithmic moment nor finite expected space is assumed. No finite-support, rationality, entropy, mean, efficiency or independence-between-targets hypothesis is imposed. The targets cannot inspect the private state or unread fair bits.
--
--   This companion theorem supplies the overall-space optimality comparison for the published goal; it is not used in the proof of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: arbitrary online sampling algorithms using CDF oracles → represented-state causal transition programs with a shared sequential fair-bit tape and access to current and previous oracle handles; reason: finite binary representations cover every physical word-RAM state without a space bound; arbitrary deterministic local transitions include all effective local computations, and only query answers enter execution
--   - generalization: Ω(log n + E[max log X_i]) → one positive real constant before every sampler, probability space, admissible environment and n ≥ 1; reason: Lean drops the asymptotic threshold n₀ and makes c uniform over samplers and environments, so it implies the source's Ω bound for every sampler and target sequence; the proof's constants (equation (78) and the output bit-length charge) are uniform and already work at n=1
--   - encoding: expected peak storage and expected maximum output logarithm → nonnegative extended integrals under onlineMeasure, with the maximum inside the integral and infinity for nontermination; reason: this preserves infinite moments; the clipped source logarithm is unchanged, and exactness makes the default outputs on nontermination immaterial
-- source:
--   Draper, Harris and Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, manuscript dated 2026-11-02. Citation basis: preprint; pinned source.pdf SHA-256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; no arXiv identifier/version exists in the artifact, so cite the dated hash-pinned submission with the paper's own result number. PDF 1 is unnumbered; For PDF pages 2–24, printed page = PDF page − 1; PDF 1 is unnumbered. Source artifact: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf. Theorem 7.3, PDF 19 / printed 18; proof PDF 17–19 / printed 16–18.

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Supplement_Observables

namespace OnlineRealSampling.Exact.Supplement

open MeasureTheory
open scoped ENNReal

/-- Theorem 7.3, PDF 19 / printed 18. One positive uniform constant before the
sampler, external probability space, causal environment and horizon. Expectations
are extended nonnegative, retaining infinite-space and infinite-log-moment cases. -/
theorem theorem_7_3 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (σ : Type) (A : Sampler σ), IsExact A →
        ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
          (env : Ξ → List ℕ → CDFOracle), AdmissibleEnv env →
          ∀ n : ℕ, 1 ≤ n →
            ENNReal.ofReal c * (ENNReal.ofReal (slog (n : ℝ)) +
              expectedMaxLog A μ env n) ≤ expectedSpace A μ env n := by sorry

end OnlineRealSampling.Exact.Supplement
