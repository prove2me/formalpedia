-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_theorem_5_6
-- name    : OnlineRealSampling.Exact.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:23.504443+00:00
-- url     : https://prove2.me/theorems/54f09a7a-195f-4b8d-a6ef-4b7ce6a1a2f5
-- title:
--   Theorem 5.6 — entropy loss of one step
-- statement:
--   Let $F$ have a valid oracle, $1\le M\le\Delta$ with $\Delta\ge1000$, and let $Z$ be uniform on $\{0,\dots,M-1\}$, independent of the fair bits. The number $T=\max\{r,s\}$ of fresh bits read by Sample$(F,(Z,M),\Delta)$ (lines 17 and 26 of Algorithm 3) satisfies
--   $$\mathbb E[T-\lg M'\mid M,X]\le\lg\frac1{f(X)}-\lg M+\frac{48\lg\Delta}{\Delta}.\qquad(26)$$
--
--   Summed over the iterations, this telescopes to the bound on the total entropy loss (Proposition 6.1).
--
--   Differences from the source:
--   - encoding: E[T − lg M′ | M, X] ≤ … → on every fibre X = x with f(x) > 0, T − lg M′ is integrable on the event {X = x} and its integral there is at most the bound times Pr(X = x); reason: equivalent on the fibres of positive probability; integrability makes the conditional expectation meaningful
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Theorem 5.6, PDF 12 / printed 11

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Theorem 5.6 (single-step entropy loss). If `Δ ≥ 1000` (and `1 ≤ M ≤ Δ`), the number
`T = max{r, s}` of fresh bits read by `Sample(F, (Z, M), Δ)` satisfies
`E[T - lg M' | M, X] ≤ lg(1/f(X)) - lg M + 48 lg Δ / Δ`; stated on every fibre `X = x` with
`f(x) > 0`, including the integrability of `T - lg M'` there. -/
theorem theorem_5_6 (w : ℕ) (O : CDFOracle) (hO : O.Valid) (M Δ : ℕ) (hM : 1 ≤ M) (hMΔ : M ≤ Δ)
    (hΔ : 1000 ≤ Δ) (x : ℕ) (hx : 0 < pmf O.F x) :
    IntegrableOn (fun p => match sampleOn w O.toOracleAccess M Δ p with
        | some out => (out.T : ℝ) - lg out.M'
        | none => 0) (sampleEvent w O.toOracleAccess M Δ x) (stepMeasure M) ∧
      ∫ p in sampleEvent w O.toOracleAccess M Δ x,
          (match sampleOn w O.toOracleAccess M Δ p with
            | some out => (out.T : ℝ) - lg out.M'
            | none => 0) ∂(stepMeasure M) ≤
        (lg (1 / pmf O.F x) - lg M + 48 * lg Δ / Δ) *
          (stepMeasure M).real (sampleEvent w O.toOracleAccess M Δ x) := by sorry

end OnlineRealSampling.Exact
