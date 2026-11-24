-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_theorem_E_1
-- name    : LagrangeRank.Debias.Supplement.theorem_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:56:28.830493+00:00
-- url     : https://prove2.me/theorems/881807d0-f05d-48e0-8aa3-6ce6767fa783
-- title:
--   Theorem E.1 (corrected: graph density) — uniform top-K error control and power
-- statement:
--   Fix bounded dynamic range $\kappa$, a positive regularization coefficient $c$, and $0<\alpha<1$. There exist constants $C_0,C>0$, uniform before all problem and score sequences, such that if $n,L\to\infty$, $p\ge C_0\log n/n$ eventually, and both rates printed in Theorem 3.3 tend to zero, then the simplified test in Remark 3.4/E.2 has both uniform properties:
--   $$\limsup\ \sup_{\theta_i^*\le\theta^*_{(K+1)}}P_{\theta^*}(\mathrm{reject})\le\alpha,\qquad
--   \inf_{\theta_i^*-\theta^*_{(K+1)}>C\sqrt{\log n/(npL)}}P_{\theta^*}(\mathrm{reject})\to1.$$
--   Both extrema range over all centered scores of the fixed bounded dynamic range, all items, and all $1\le K<n$; equivalently each assertion is an eventual bound uniform over these objects, avoiding defaults for an empty alternative class. The test lowers only coordinate $i$ and compares it to the $(K+1)$-st largest debiased score, with multiplicities. Equal-score nulls are retained through the weak inequality.
--
--   The density premise is a disclosed necessary correction. Without it, $p=n^{-3}$ and $L=n^{10}$ satisfy the two printed rates but have an empty graph with probability tending to one. The centered score $(1,0,\ldots,0)$ has top-one gap 1, while the proposed zero-extension test has rejection probability tending to zero. DISPROOF.md gives the full calculation.
--
--   Differences from the source:
--   - correction: conditions of Theorem 3.3, with no density threshold → also p≥C0 log n/n for sufficiently large fixed C0; reason: Appendix D requires the H.1 graph event; the sparse sequence p=n^(−3), L=n^10 is a fixed-gap counterexample to the printed power claim; these sparse disconnected sequences are the excluded cases
--   - reading: asymptotic Type I ≤α and uniform power in E.1 → eventual α+ε and 1−ε bounds, uniform over the source nulls and separated alternatives; reason: the proof on pp. 57–58 states α+o(1) and a high-probability power bound; no finite-sample exact level is claimed
--   - encoding: sample size n and repeated-comparison count L tend to infinity → a separate sequence index t, dimensions n(t), L(t), and finite product probability spaces; reason: the law at each problem size is exactly (2.1); both graph and comparison randomness remain
--   - encoding: inverse in (3.10) on the high-probability invertible graph event → the actual Matrix.inv, with zero on singular inputs; reason: under the stated sufficiently large graph-density constant the exceptional probability vanishes; no population inverse or CLIME estimate is substituted
--   - encoding: order statistics including equal-score nulls → descending order with multiplicities and increasing-index tie resolution; reason: order statistic values are unaffected by tie resolution; θ_i≤θ_(K+1) remains weak, so boundary nulls are not excluded
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 57, Theorem E.1

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_Ranking

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
/-- Corrected E.1 with the density premise used by Appendix D; uniform null error and power. -/
theorem theorem_E_1 (κ c α : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hα : 0 < α ∧ α < 1) :
    ∃ C0 C : ℝ, 0 < C0 ∧ 0 < C ∧
    ∀ (n L : ℕ → ℕ) (p : ℕ → unitInterval),
      Regime n L p → Density C0 n p → Rates33 n L p →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
        ∀ (θ : Vec (n t)) (i K : Fin (n t)),
          Parameter κ θ → 1 ≤ K.val → θ i ≤ orderValue θ K →
          (dataLaw (L t) (p t) θ {s | topReject (p t) c α i K s}).toReal ≤ α + ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
        ∀ (θ : Vec (n t)) (i K : Fin (n t)),
          Parameter κ θ → 1 ≤ K.val →
          C * signalScale (n t) (L t) (p t) < θ i - orderValue θ K →
          1 - ε ≤ (dataLaw (L t) (p t) θ {s | topReject (p t) c α i K s}).toReal) := by sorry

end LagrangeRank.Debias.Supplement
