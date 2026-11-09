-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_theorem_5_8
-- name    : OnlineRealSampling.Exact.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:13:24.057033+00:00
-- url     : https://prove2.me/theorems/6a41ea2b-f8ad-45bb-85dd-f99903f978e8
-- title:
--   Theorem 5.8 — running time with an accuracy-efficient oracle
-- statement:
--   Let $F$ have a valid oracle whose cost function $C_F$ is accuracy efficient with polynomial $g$, let $1\le M\le\Delta$, and let $Z$ be uniform on $\{0,\dots,M-1\}$, independent of the fair bits. For every $x$ with $p=f(x)>0$, conditionally on $X=x$, the expected running time of Sample$(F,(Z,M),\Delta)$ is
--   $$O\big(C_F(x,\Delta)+\log(x+1/p)\,C_F(2x,1/p)\big),\qquad(36)$$
--   with a constant depending only on $g$.
--
--   Index efficiency is not assumed.
--
--   Differences from the source:
--   - encoding: a bound conditional on X = x → the integral over the event {X = x} is at most the bound times Pr(X = x), for every x with f(x) > 0; reason: equivalent on the fibres of positive probability, which are exactly those with f(x) > 0
--   - encoding: expected values of resources that may be unbounded → lower Lebesgue integrals in [0, ∞], with the resource equal to ∞ on non-termination; reason: no junk value; the same instances, since termination is almost sure
--   - generalization: O(·) bounds for a fixed word size w ≥ 1 → one constant K valid for every word size w ≥ 1; reason: the source's constants do not depend on w; the statement specializes to each fixed w
--   - reading: Word RAM in which big-integer multiplication and division cost O(k log k) or Θ(k²) → concrete charged primitives: addition, subtraction and comparison cost limbs(a)+limbs(b); multiplication and division cost limbs(a)·limbs(b)+limbs(a)+limbs(b); shifts and powers of two cost the limbs of the result plus 1; bit length costs 1; every machine step costs at least 1; reason: the source leaves the multiplication algorithm open and names schoolbook as one option; C_F is assumed to dominate basic arithmetic under either choice
--   - encoding: accuracy efficiency (7) as a bound on a quotient → the multiplicative form C(x,ν′) ≤ g(log ν′/log ν)·C(x,ν); reason: a cost function is positive (it dominates the cost of an arithmetic operation), so the two forms agree
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Theorem 5.8, PDF 13 / printed 12; proof PDF 13 / printed 12

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Theorem 5.8 (accuracy-efficient oracles). If the oracle's cost function is accuracy efficient
with polynomial `g`, then conditionally on `X = x` (`p = f(x) > 0`) the expected running time of
`Sample(F, (Z, M), Δ)` is `O(C_F(x, Δ) + log(x + 1/p) C_F(2x, 1/p))`, the constant depending only
on `g`. -/
theorem theorem_5_8 (g : Polynomial ℝ) :
    ∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ (O : CDFOracle) (C : ℝ → ℝ → ℝ), O.Valid →
      CostBound w O.toOracleAccess C → AccuracyEfficient g C →
      ∀ M Δ : ℕ, 1 ≤ M → M ≤ Δ → ∀ x : ℕ, 0 < pmf O.F x →
        ∫⁻ p in sampleEvent w O.toOracleAccess M Δ x,
            sampleRes w O.toOracleAccess M Δ Usage.time p ∂(stepMeasure M) ≤
          ENNReal.ofReal (K * (C x Δ + slog (x + 1 / pmf O.F x) * C (2 * x) (1 / pmf O.F x))) *
            stepMeasure M (sampleEvent w O.toOracleAccess M Δ x) := by sorry

end OnlineRealSampling.Exact
