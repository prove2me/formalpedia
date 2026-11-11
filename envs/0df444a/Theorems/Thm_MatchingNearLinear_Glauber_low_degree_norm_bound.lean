-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_low_degree_norm_bound
-- name    : MatchingNearLinear.Glauber.low_degree_norm_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:55:32.172535+00:00
-- url     : https://prove2.me/theorems/39f2b926-366e-4d9e-ba18-205ad959a023
-- title:
--   Lemma 3.3 — Low-degree norm bound
-- statement:
--   Let $N\ge1$ and let $p$ be a probability law on a downward-closed subset support with at least two states. Suppose the insertion ratios are bounded by $\kappa\ge1$ and every feasible occupied marginal under positive pinning is at least $b$, where $0<b\le1$. For every positive pin $\tau$, every integer $j\ge0$, and every polynomial $f$ of degree at most $j$ on the residual support of $\nu=p^\tau$,
--
--   $$\|f\|_{\infty,\nu}\le\left(1+N\sqrt{\frac{1+\kappa}{b}}\right)^j\|f\|_{2,\nu}.$$
--
--   Singleton residual supports and degree zero are included. No spectral stability hypothesis is imposed. This gives the norm input to Proposition 3.1, uniformly under further positive pinnings.
--
--   Differences from the source:
--   - encoding: a probability law positive on its actual subset support → a nonnegative normalized mass function on all subsets, with functions on its strictly positive support subtype; reason: zero-weight configurations add no instances or hypotheses
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma 3.3, printed p. 12 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_SubsetLaws

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem low_degree_norm_bound
    (N : ℕ) (hN : 1 ≤ N) (p : Config N → ℝ) (hp : IsSubsetLaw p)
    (hd : DownwardClosed p) (hnt : 2 ≤ Fintype.card (Support p))
    (κ b : ℝ) (hk : 1 ≤ κ) (hb : 0 < b ∧ b ≤ 1)
    (hratio : RatioBound p κ) (hlower : OccupiedLowerBound p b)
    (τ : Config N) (hτ : 0 < p τ) (j : ℕ)
    (f : Support (positivePin p τ) → ℝ) (hf : f ∈ polynomialSpace (positivePin p τ) j) :
    normInfinity f ≤ (1+(N:ℝ)*Real.sqrt ((1+κ)/b))^j *
      normTwo (supportMass (positivePin p τ)) f := by sorry

end MatchingNearLinear.Glauber
