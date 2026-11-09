-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_5_11
-- name    : OnlineRealSampling.Exact.proposition_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:56.542896+00:00
-- url     : https://prove2.me/theorems/30e65ed1-434a-4382-9735-4ba1672a78f7
-- title:
--   Proposition 5.11 — temporary space of Sample
-- statement:
--   Let $F$ have a valid oracle, $1\le M\le\Delta$, and let $Z$ be uniform on $\{0,\dots,M-1\}$, independent of the fair bits. Let $S$ be the temporary space of Sample$(F,(Z,M),\Delta)$. There are absolute constants $c,K,K'$ such that, conditionally on $X$,
--   $$\Pr\Big(S\ge c\Big[\log\Big(X+\frac{\Delta}{f(X)}\Big)+\lambda\Big]\ \Big|\ X\Big)\le K2^{-\lambda}\qquad(\lambda\ge1),\qquad(49)$$
--   $$\mathbb E[S\mid X]\le K'\log\Big(X+\frac{\Delta}{f(X)}\Big).\qquad(50)$$
--
--   Both the tail and the mean are part of the statement.
--
--   Differences from the source:
--   - reading: conditioned on X, there is some constant c with Pr(…) ≤ O(2^{−λ}) → constants c, K, K′ chosen once, before the oracle, M, Δ and x; reason: the stronger of the two readings; the mean bound (50) requires c not to depend on X
--   - encoding: a bound conditional on X = x → the integral over the event {X = x} is at most the bound times Pr(X = x), for every x with f(x) > 0; reason: equivalent on the fibres of positive probability, which are exactly those with f(x) > 0
--   - encoding: expected values of resources that may be unbounded → lower Lebesgue integrals in [0, ∞], with the resource equal to ∞ on non-termination; reason: no junk value; the same instances, since termination is almost sure
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 5.11, PDF 14 / printed 13

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 5.11 (temporary space). The temporary space `S` of `Sample(F, (Z, M), Δ)`
satisfies, conditionally on `X`, `Pr(S ≥ c[log(X + Δ/f(X)) + λ] | X) ≤ O(2^{-λ})` for all
`λ ≥ 1`, and `E[S | X] ≤ O(log(X + Δ/f(X)))`, with absolute constants. -/
theorem proposition_5_11 :
    ∃ c K K' : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ O : CDFOracle, O.Valid → ∀ M Δ : ℕ, 1 ≤ M → M ≤ Δ →
      ∀ x : ℕ, 0 < pmf O.F x →
        (∀ l : ℝ, 1 ≤ l →
          stepMeasure M {p | p ∈ sampleEvent w O.toOracleAccess M Δ x ∧
              ENNReal.ofReal (c * (slog (x + Δ / pmf O.F x) + l)) ≤
                sampleRes w O.toOracleAccess M Δ Usage.space p} ≤
            ENNReal.ofReal (K * (2 : ℝ) ^ (-l)) *
              stepMeasure M (sampleEvent w O.toOracleAccess M Δ x)) ∧
        ∫⁻ p in sampleEvent w O.toOracleAccess M Δ x,
            sampleRes w O.toOracleAccess M Δ Usage.space p ∂(stepMeasure M) ≤
          ENNReal.ofReal (K' * slog (x + Δ / pmf O.F x)) *
            stepMeasure M (sampleEvent w O.toOracleAccess M Δ x) := by sorry

end OnlineRealSampling.Exact
