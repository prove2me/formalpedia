-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_12
-- name    : OrderedSearchExact.Exact.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:06.83262+00:00
-- url     : https://prove2.me/theorems/aaf49aa8-d044-4e13-af57-ab3f7057807d
-- title:
--   Lemma 4.12 — large-rate bound and D=2 exactifier criterion
-- statement:
--   For every $n$, every real $D$ and extended nonnegative rate $\lambda$ with $\lambda\ge Dn>0$,
--
--   $$\sum_{j=1}^{n-1}g_{\lambda,n}(j)\le\frac1{(e^D-1)(1-e^{-2Dn})}.$$
--
--   The constant $D=2$ meets the sufficient decay criterion. For any compactly supported probability density $h$, if both physical-rate mixtures at centers $\alpha,\beta$ are at least $2n$ almost surely, the coefficients of $q_{S_{\alpha e^Y}+A_{\beta e^Y}}$ satisfy $2\sum_j|a_j|<1$. The first bound keeps every positive $D$, and the second supplies the strict condition needed by the exactifier.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - encoding: expectations under a compactly supported probability density → full Lebesgue integrals against a measurable nonnegative density of mass one and almost-sure compact support; reason: the same density class is used; bounded coefficient kernels are integrable against every such density
--   - encoding: rates in [0,infinity], with limiting endpoints → ENNReal rates with explicit zero and infinity branches; reason: the extended supremum never defaults to a finite real value; the endpoint polynomials are the prescribed limits
--   - encoding: D=2 suffices, using the bound 4/((exp D-1)(1-exp(-2Dn)))<1 in the proof → also records DecayConstant 2, the uniform criterion with n=2 in its denominator; reason: for D>0 the denominator increases with n; this is the same sufficient numerical condition, not an additional hypothesis
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.12, p.22 (PDF p.22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Analysis

namespace OrderedSearchExact.Exact

theorem lemma_4_12 (n : ℕ) :
    (∀ D : ℝ, ∀ lam : Rate, 0 < D * n → ENNReal.ofReal (D * n) ≤ lam →
      (∑ i : Fin (n - 1), g n lam i) ≤
        1 / ((Real.exp D - 1) * (1 - Real.exp (-2 * D * n)))) ∧
    DecayConstant 2 ∧
    (∀ (h : ℝ → ℝ), IsDensity h → ∀ α β : Rate,
      AlmostSure h (fun y => ENNReal.ofReal (2 * n) ≤ physicalRate α y) →
      AlmostSure h (fun y => ENNReal.ofReal (2 * n) ≤ physicalRate β y) →
      mass (hybrid n h α β) < 1) := by sorry

end OrderedSearchExact.Exact
