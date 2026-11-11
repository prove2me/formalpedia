-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_dirichlet_form_bound
-- name    : MatchingNearLinear.Glauber.dirichlet_form_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:55:38.683614+00:00
-- url     : https://prove2.me/theorems/fd78d652-75e6-4463-9484-adea83670edb
-- title:
--   Lemma 3.2 — Dirichlet-form bound
-- statement:
--   Let $N\ge1$ and let $p$ be a probability law positive on a downward-closed support $\Omega\subseteq2^{[N]}$ containing at least two states. Let $r=\max_{S\in\Omega}|S|$. Assume field-dynamics spectral stability with a nonincreasing rate $C:[0,1)\to[1,\infty)$, with finite $I=\int_0^1(C(t)-1)/(1-t)\,dt$, and insertion ratios at most $\kappa>0$. For every $0\le j<r$ and real $f$ on $\Omega$,
--
--   $$\mathcal E_{\rm GD}(f,f)\ge\frac{(j+1)e^{-I}}{N(1+\kappa)}\|f-\Pi_jf\|_2^2.$$
--
--   Here $\Pi_j$ is the genuine weighted projection onto occupation polynomials of degree at most $j$. No occupied-marginal lower bound is assumed. This is the first input to the low-degree LSI criterion.
--
--   Differences from the source:
--   - encoding: a probability law positive on its actual subset support → a nonnegative normalized mass function on all subsets, with functions on its strictly positive support subtype; reason: zero-weight configurations add no instances or hypotheses
--   - encoding: weighted L2 orthogonal projection → the unique member of the subspace satisfying all weighted orthogonality equations, selected noncomputably; reason: a positive law on a finite support guarantees existence and uniqueness; the invalid-weight fallback is never used
--   - encoding: finite improper stability integral → nonnegative extended Lebesgue integral with an explicit finiteness hypothesis before conversion to a real; reason: prevents a divergent integral from receiving a default finite value
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma 3.2, printed p. 12 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_SubsetLaws

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem dirichlet_form_bound
    (N : ℕ) (hN : 1 ≤ N) (p : Config N → ℝ) (hp : IsSubsetLaw p)
    (hd : DownwardClosed p) (hnt : 2 ≤ Fintype.card (Support p))
    (C : ℝ → ℝ) (hC : RateConditions C) (hs : SpectralStability p C)
    (κ : ℝ) (hk : 0 < κ) (hratio : RatioBound p κ)
    (j : ℕ) (hj : j < rank p) (f : Support p → ℝ) :
    energy (supportMass p) (subsetGlauber p) f f ≥
      (((j:ℝ)+1) * Real.exp (-(stabilityIntegral C).toReal) / ((N:ℝ)*(1+κ))) *
      normSq (supportMass p) (f - polynomialProjection p j f) := by sorry

end MatchingNearLinear.Glauber
