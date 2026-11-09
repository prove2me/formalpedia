-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_6_1
-- name    : OnlineRealSampling.Exact.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:16:56.588171+00:00
-- url     : https://prove2.me/theorems/fe340d4d-7814-4af3-96f8-d741096592cd
-- title:
--   Proposition 6.1 — telescoped entropy loss of Algorithm 2
-- statement:
--   Let $\epsilon\in[0,1]$, and let the targets be chosen by an admissible adaptive environment. For every $n\ge1$, the entropy loss after the first $n$ iterations of Algorithm 2 is well defined and
--   $$L_n\le\lg\Delta_n+48\sum_{i=1}^n\frac{\lg\Delta_i}{\Delta_i},\qquad(51)$$
--   where $\Delta_i$ is the value of $\Delta$ used in iteration $i$.
--
--   With the schedule of Algorithm 2 this gives Theorem 4.2.
--
--   Differences from the source:
--   - encoding: L_n = E[T_n − Σ lg(1/f_i(X_i))] → integrability of the centred variable T_n − Σ lg(1/f_i(X_i)) is asserted, and L_n is its integral; reason: the source's expectation exists; asserting integrability rules out the default value 0 of a non-integrable integral
--   - reading: target F_i chosen from previous outputs and external randomness, independently of the sampler's state given X_1,…,X_{i-1} → F_i = env(ξ, [X_1,…,X_{i-1}]) with ξ ∼ μ independent of the fair bits, env measurable in ξ; reason: the source's information restriction, with external randomness drawn once as a seed; measurability is the convention needed for the expectations to be defined
--   - encoding: for every n → for every n ≥ 1; reason: L_n is defined in (3) for n ≥ 1 and Δ_n is the value of Δ used in iteration n ≥ 1 (Algorithm 2 starts with Δ = 0, so lg Δ_0 is undefined); n = 0 is not an instance of the source
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 6.1, PDF 15 / printed 14

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Online

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 6.1 (telescoping entropy loss). For every `n ≥ 1` and every admissible adaptive
environment, the entropy loss of the first `n` iterations of Algorithm 2 (any `ε ∈ [0,1]`) is
well defined and `L_n ≤ lg Δ_n + 48 ∑_{i=1}^n lg Δ_i / Δ_i`. -/
theorem proposition_6_1 (w : ℕ) {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (env : Ξ → List ℕ → CDFOracle) (henv : AdmissibleEnv env) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (lossVar w ε env n) (onlineMeasure μ) ∧
      entropyLoss w μ ε env n ≤
        lg (deltaSched ε n) + 48 * ∑ i ∈ Finset.Icc 1 n, lg (deltaSched ε i) / deltaSched ε i := by sorry

end OnlineRealSampling.Exact
