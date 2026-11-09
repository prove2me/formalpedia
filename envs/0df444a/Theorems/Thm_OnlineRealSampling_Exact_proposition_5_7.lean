-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_5_7
-- name    : OnlineRealSampling.Exact.proposition_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:13.567204+00:00
-- url     : https://prove2.me/theorems/c008b4c8-74ee-4a0b-9a88-1e22679bac40
-- title:
--   Proposition 5.7 — running time with an arbitrary oracle
-- statement:
--   Let $F$ have a valid oracle with cost function $C_F$ (no efficiency assumed), let $1\le M\le\Delta$, and let $Z$ be uniform on $\{0,\dots,M-1\}$, independent of the fair bits. For every $x$ with $p=f(x)>0$, conditionally on $X=x$ the expected running time of Sample$(F,(Z,M),\Delta)$ is at most
--   $$K\Big(C_F(x,2\Delta/p)+\log(x+1/p)\sum_{j=0}^\infty2^{-j}C_F(2x,2^j/p)\Big),\qquad(32)$$
--   and the expected numbers of oracle calls and of big-integer arithmetic operations are at most $K\log(x+1/p)$, for an absolute constant $K$.
--
--   The series may diverge. Theorems 5.8 and 5.9 evaluate it for efficient oracles.
--
--   Differences from the source:
--   - encoding: a bound conditional on X = x → the integral over the event {X = x} is at most the bound times Pr(X = x), for every x with f(x) > 0; reason: equivalent on the fibres of positive probability, which are exactly those with f(x) > 0
--   - encoding: expected values of resources that may be unbounded → lower Lebesgue integrals in [0, ∞], with the resource equal to ∞ on non-termination; reason: no junk value; the same instances, since termination is almost sure
--   - encoding: each IntervalSample iteration evaluates F⁺(X_mid, t) and, if needed, F⁻(X_mid, t) → one oracle call φ(X_mid, t+1) per iteration, from which both bounds are formed; reason: both bounds are φ(X_mid, t+1) ± 2^{-(t+1)} by (5); the deterministic oracle returns the same value, so this implements the pseudocode with at most the source's number of calls
--   - generalization: O(·) bounds for a fixed word size w ≥ 1 → one constant K valid for every word size w ≥ 1; reason: the source's constants do not depend on w; the statement specializes to each fixed w
--   - reading: Word RAM in which big-integer multiplication and division cost O(k log k) or Θ(k²) → concrete charged primitives: addition, subtraction and comparison cost limbs(a)+limbs(b); multiplication and division cost limbs(a)·limbs(b)+limbs(a)+limbs(b); shifts and powers of two cost the limbs of the result plus 1; bit length costs 1; every machine step costs at least 1; reason: the source leaves the multiplication algorithm open and names schoolbook as one option; C_F is assumed to dominate basic arithmetic under either choice
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 5.7, PDF 12 / printed 11; proof PDF 13 / printed 12

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 5.7 (general oracle-cost bound). Conditionally on `X = x` (`p = f(x) > 0`), the
expected running time of `Sample(F, (Z, M), Δ)` is
`O(C_F(x, 2Δ/p) + log(x + 1/p) ∑_{j ≥ 0} 2^{-j} C_F(2x, 2^j/p))`, and the expected numbers of
oracle calls and of arithmetic operations are `O(log(x + 1/p))`. No efficiency is assumed. -/
theorem proposition_5_7 :
    ∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ (O : CDFOracle) (C : ℝ → ℝ → ℝ), O.Valid →
      CostBound w O.toOracleAccess C → ∀ M Δ : ℕ, 1 ≤ M → M ≤ Δ → ∀ x : ℕ, 0 < pmf O.F x →
        ∫⁻ p in sampleEvent w O.toOracleAccess M Δ x,
            sampleRes w O.toOracleAccess M Δ Usage.time p ∂(stepMeasure M) ≤
          ENNReal.ofReal K * (ENNReal.ofReal (C x (2 * Δ / pmf O.F x)) +
            ENNReal.ofReal (slog (x + 1 / pmf O.F x)) *
              ∑' j : ℕ, ENNReal.ofReal (C (2 * x) (2 ^ j / pmf O.F x) / 2 ^ j)) *
            stepMeasure M (sampleEvent w O.toOracleAccess M Δ x) ∧
        ∫⁻ p in sampleEvent w O.toOracleAccess M Δ x,
            sampleRes w O.toOracleAccess M Δ Usage.calls p ∂(stepMeasure M) ≤
          ENNReal.ofReal (K * slog (x + 1 / pmf O.F x)) *
            stepMeasure M (sampleEvent w O.toOracleAccess M Δ x) ∧
        ∫⁻ p in sampleEvent w O.toOracleAccess M Δ x,
            sampleRes w O.toOracleAccess M Δ Usage.ops p ∂(stepMeasure M) ≤
          ENNReal.ofReal (K * slog (x + 1 / pmf O.F x)) *
            stepMeasure M (sampleEvent w O.toOracleAccess M Δ x) := by sorry

end OnlineRealSampling.Exact
