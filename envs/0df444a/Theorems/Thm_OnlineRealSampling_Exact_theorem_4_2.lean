-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_theorem_4_2
-- name    : OnlineRealSampling.Exact.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:17:08.083034+00:00
-- url     : https://prove2.me/theorems/f35aa7b9-9fd3-432e-9537-e573e0b8f2fc
-- title:
--   Theorem 4.2 — entropy loss $\epsilon n+11\lg(n+2)$
-- statement:
--   Let $\epsilon\in[0,1]$, and let the targets be chosen by an admissible adaptive environment. For every $n\ge1$, the entropy loss after $n$ iterations of the sampling loop of Algorithm 2 is well defined and
--   $$L_n\le\epsilon n+11\lg(n+2).\qquad(11)$$
--
--   With $\epsilon=0$ this is the logarithmic entropy loss of Theorem 1.2; with $\epsilon>0$ it trades entropy for bounded persistent state.
--
--   Differences from the source:
--   - encoding: L_n = E[T_n − Σ lg(1/f_i(X_i))] → integrability of the centred variable T_n − Σ lg(1/f_i(X_i)) is asserted, and L_n is its integral; reason: the source's expectation exists; asserting integrability rules out the default value 0 of a non-integrable integral
--   - reading: target F_i chosen from previous outputs and external randomness, independently of the sampler's state given X_1,…,X_{i-1} → F_i = env(ξ, [X_1,…,X_{i-1}]) with ξ ∼ μ independent of the fair bits, env measurable in ξ; reason: the source's information restriction, with external randomness drawn once as a seed; measurability is the convention needed for the expectations to be defined
--   - encoding: after n iterations → for every n ≥ 1; reason: L_n is defined in (3) for n ≥ 1, and Algorithm 2 states its guarantee "after any n ≥ 1 iterations"
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Theorem 4.2, PDF 9 / printed 8; restated and proved on PDF 15 / printed 14

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Online

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Theorem 4.2 (entropy loss of Algorithm 2). For every `ε ∈ [0,1]`, every `n ≥ 1` and every
admissible adaptive environment, the entropy loss after `n` iterations of Algorithm 2 is well
defined and `L_n ≤ ε n + 11 lg(n + 2)`. -/
theorem theorem_4_2 (w : ℕ) {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (env : Ξ → List ℕ → CDFOracle) (henv : AdmissibleEnv env) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (lossVar w ε env n) (onlineMeasure μ) ∧
      entropyLoss w μ ε env n ≤ ε * n + 11 * lg (n + 2) := by sorry

end OnlineRealSampling.Exact
