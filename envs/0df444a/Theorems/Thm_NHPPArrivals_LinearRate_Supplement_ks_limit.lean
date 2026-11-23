-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_Supplement_ks_limit
-- name    : NHPPArrivals.LinearRate.Supplement.ks_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:11:59.480385+00:00
-- url     : https://prove2.me/theorems/73458938-bd31-4ecb-9e0b-9f48ebb0f971
-- title:
--   THEOREM 3 — conditional empirical CU KS statistic converges almost surely to the degree
-- statement:
--   Let $N$ be an NHPP of rate $\lambda$ on $[0,T]$ under §3.2's standing assumptions, and let $Y_n$ on a common probability space have the law of its scaled ordered arrivals conditioned on $N(T)=n$. Define the actual empirical statistic $D_n=\sup_{0\le t\le1}|\bar F_n(t)-t|$, and put $F(t)=\Lambda(tT)/\Lambda(T)$. Then
--   $$D_n\longrightarrow D=\sup_{0\le t\le1}|F(t)-t|\quad\text{almost surely}.$$
--   The limit is the published degree of nonhomogeneity, using absolute error on the full unit interval. It describes the CU KS statistic of conditional NHPP observations.
--
--   Differences from the source:
--   - encoding: An NHPP with the standing assumptions of §3.2. → A probability space, measurable counts and epochs, independent Poisson increments, T>0, and AdmissibleRate on [0,T].; reason: These spell out the source model without continuity, boundedness or an assumed conditional law.
--   - generalization: Almost-sure convergence of conditional samples as n grows, without specifying the coupling between sample sizes. → The conclusion holds for every common probability space carrying rows with the actual conditional vector laws.; reason: This includes the nested iid/order-statistic coupling; the distribution-free exponential empirical-cdf bound makes exceptional probabilities summable for every coupling. No case of the source is excluded.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, DOI 10.1287/msom.2014.0490, p. 471, THEOREM 3, PDF 8

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_Supplement_KSTest

namespace NHPPArrivals.LinearRate.Supplement

open MeasureTheory Filter Topology

theorem ks_limit {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (lam : ℝ → ℝ) (T : ℝ) (hrate : AdmissibleRate lam T)
    (N : ℝ → Ω → ℕ) (X : ℕ → Ω → ℝ) (hN : IsNHPP P lam T N X)
    (Y : (n : ℕ) → Ξ → Fin n → ℝ) (hY : ConditionalRows P N X T Q Y) :
    ∀ᵐ ξ ∂Q, Tendsto (fun n : ℕ => ks (Y n ξ))
      atTop (𝓝 (degree (condCdf lam T))) := by sorry

end NHPPArrivals.LinearRate.Supplement
