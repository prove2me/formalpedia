-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_symmetric_lift_covariance
-- name    : MatchingNearLinear.Glauber.symmetric_lift_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:56:28.539557+00:00
-- url     : https://prove2.me/theorems/7d12439d-b594-45f4-a452-fd0758c6a9d6
-- title:
--   Lemma 3.6 — Covariance of the symmetric lift
-- statement:
--   Fix $N\ge1$ and a probability law $p$ on a downward-closed subset support with at least two states. Let $\widehat p_K$ be its symmetric lift with $K>N$ auxiliary sites, and let $C^*(t)$ be the least admissible covariance coefficient at least one over positive pinnings of $(1-t)*p$. There are constants $a_p\ge0$ and $K_0>N$, depending only on this fixed law, such that for every $K\ge K_0$, every $2\le l\le K$, and every feasible positive pin of the lift leaving residual size $l$,
--
--   $$\operatorname{Cov}(Z)\preceq\left[C^*(1-l/K)+\frac{a_p}{K}\right]\operatorname{Diag}(EZ).$$
--
--   The error and threshold are simultaneous over all pins and residual sizes. This transfers scalar-field covariance control to the homogeneous lift without adding a marginal lower bound.
--
--   Differences from the source:
--   - encoding: a probability law positive on its actual subset support → a nonnegative normalized mass function on all subsets, with functions on its strictly positive support subtype; reason: zero-weight configurations add no instances or hypotheses
--   - encoding: an error O_mu(K^-1), uniformly in the pin and residual size → one nonnegative error constant and one threshold after the fixed law, before K, the pin and residual size; reason: expands the uniform asymptotic quantifiers exactly
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma 3.6, printed p. 15 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_SymmetricLift

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem symmetric_lift_covariance
    (N : ℕ) (hN : 1 ≤ N) (p : Config N → ℝ) (hp : IsSubsetLaw p)
    (hd : DownwardClosed p) (hnt : 2 ≤ Fintype.card (Support p)) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ K₀ : ℕ, N < K₀ ∧
      ∀ K : ℕ, K₀ ≤ K → ∀ l : ℕ, 2 ≤ l → l ≤ K →
      ∀ τ : Config (N+K), 0 < pinMass (symmetricLift p K) τ → τ.card + l = K →
      CovarianceBound (positivePin (symmetricLift p K) τ)
        (leastRate p (1-(l:ℝ)/K) + a/K) := by sorry

end MatchingNearLinear.Glauber
