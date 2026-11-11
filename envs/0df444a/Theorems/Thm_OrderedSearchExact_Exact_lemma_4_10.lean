-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_10
-- name    : OrderedSearchExact.Exact.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:10.096218+00:00
-- url     : https://prove2.me/theorems/58642ef9-1249-4122-be98-199bdd3422ac
-- title:
--   Lemma 4.10 — first move at the zero-rate endpoint
-- statement:
--   For every $n$, any compactly supported probability density $h$, and a nonnegative center $\beta$, if $0\le\beta e^Y\le1$ almost surely, then
--
--   $$q_{S_{\beta e^Y}+A_0}(e^{i\theta})\ge0\qquad(\theta\in\mathbb R).$$
--
--   In particular, for every $W>0$ the quartic packet satisfies $\Gamma_S(0)\ge e^{-W}$. This includes $\beta=0$ and supplies initialization, which the positive-center lemmas do not cover.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - encoding: expectations under a compactly supported probability density → full Lebesgue integrals against a measurable nonnegative density of mass one and almost-sure compact support; reason: the same density class is used; bounded coefficient kernels are integrable against every such density
--   - encoding: rates in [0,infinity], with limiting endpoints → ENNReal rates with explicit zero and infinity branches; reason: the extended supremum never defaults to a finite real value; the endpoint polynomials are the prescribed limits
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.10, p.21 (PDF p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Greedy

namespace OrderedSearchExact.Exact

theorem lemma_4_10 (n : ℕ) :
    (∀ (h : ℝ → ℝ), IsDensity h → ∀ β : Rate,
      AlmostSure h (fun y => 0 ≤ physicalRate β y ∧ physicalRate β y ≤ 1) →
      Nonnegative (hybrid n h β 0)) ∧
    (∀ W : ℝ, 0 < W →
      ENNReal.ofReal (Real.exp (-W)) ≤ gammaS n (quarticDensity W) 0) := by sorry

end OrderedSearchExact.Exact
