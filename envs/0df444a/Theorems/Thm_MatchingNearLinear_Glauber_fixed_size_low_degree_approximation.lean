-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_fixed_size_low_degree_approximation
-- name    : MatchingNearLinear.Glauber.fixed_size_low_degree_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:55:34.789837+00:00
-- url     : https://prove2.me/theorems/bd285700-32f8-419f-88c4-851efe666d98
-- title:
--   Proposition 3.4 — Low-degree approximation for fixed-size sets
-- statement:
--   Let $p$ be a probability law on $r$-element subsets of $[N]$, where $r\ge1$. Let $P_r$ be the down–up walk, $V_j$ the span of occupation monomials of degree at most $j$, and $\Pi_j$ its weighted orthogonal projection. For every $2\le l\le r$, assume $0\le\delta_l<l-1$ and that every feasible positive pin leaving residual size $l$ satisfies $\operatorname{Cov}(X)\preceq(1+\delta_l)\operatorname{Diag}(EX)$. Then for every real function $f$ on the actual support and every $0\le j<r$,
--
--   $$r\mathcal E_{P_r}(f,f)\ge(j+1)\prod_{l=2}^{r-j}\left(1-\frac{\delta_l}{l-1}\right)\|f-\Pi_jf\|_2^2.$$
--
--   The empty product is one. A uniform bound $1+\delta$, $0\le\delta<1$, is included by setting every $\delta_l=\delta$. Downward closure and occupied-marginal lower bounds are not hypotheses. This supplies the fixed-size approximation estimate used in the analytic criterion.
--
--   Differences from the source:
--   - encoding: a probability law positive on its actual subset support → a nonnegative normalized mass function on all subsets, with functions on its strictly positive support subtype; reason: zero-weight configurations add no instances or hypotheses
--   - encoding: weighted L2 orthogonal projection → the unique member of the subspace satisfying all weighted orthogonality equations, selected noncomputably; reason: a positive law on a finite support guarantees existence and uniqueness; the invalid-weight fallback is never used
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Proposition 3.4, printed p. 13 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_SubsetLaws

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem fixed_size_low_degree_approximation
    (N r : ℕ) (hr : 1 ≤ r) (p : Config N → ℝ) (hp : IsSubsetLaw p)
    (homogeneous : ∀ S, 0 < p S → S.card = r)
    (δ : ℕ → ℝ) (hδ : ∀ l, 2 ≤ l → l ≤ r → 0 ≤ δ l ∧ δ l < (l:ℝ)-1)
    (hcov : ∀ l, 2 ≤ l → l ≤ r → ∀ τ, 0 < pinMass p τ → τ.card + l = r →
      CovarianceBound (positivePin p τ) (1+δ l))
    (j : ℕ) (hj : j < r) (f : Support p → ℝ) :
    (r:ℝ) * energy (supportMass p) (downUp p r) f f ≥
      ((j:ℝ)+1) * (∏ l ∈ Finset.Icc 2 (r-j), (1-δ l / ((l:ℝ)-1))) *
      normSq (supportMass p) (f - polynomialProjection p j f) := by sorry

end MatchingNearLinear.Glauber
