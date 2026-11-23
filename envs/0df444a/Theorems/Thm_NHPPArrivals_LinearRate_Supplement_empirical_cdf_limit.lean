-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_Supplement_empirical_cdf_limit
-- name    : NHPPArrivals.LinearRate.Supplement.empirical_cdf_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:09:28.587487+00:00
-- url     : https://prove2.me/theorems/2e5ec72d-326b-4c06-b0b9-a87e9e766823
-- title:
--   THEOREM 2 (corrected: indicator index) — conditional empirical cdf converges uniformly almost surely
-- statement:
--   Let $N$ have rate $c\lambda$ on $[0,T]$, for any $c>0$, under the general standing rate assumptions. On a common probability space, for every $n$ let $Y_n$ have the full vector law of $(X_1/T,\ldots,X_n/T)$ conditioned on $N(T)=n$. With $\bar F_n$ the empirical cdf of $Y_n$ and $F(t)=\Lambda(tT)/\Lambda(T)$,
--   $$\sup_{0\le t\le1}|\bar F_n(t)-F(t)|\longrightarrow0\quad\text{almost surely as }n\to\infty.$$
--   This is the NHPP conditional empirical-cdf limit, not a limit along a single trajectory with a finite number of arrivals. It retains the general integrable-rate domain and the specified cdf.
--
--   Differences from the source:
--   - encoding: An NHPP with the standing assumptions of §3.2. → A probability space, measurable counts and epochs, independent Poisson increments, T>0, and AdmissibleRate on [0,T].; reason: These spell out the source model without continuity, boundedness or an assumed conditional law.
--   - correction: The sum in (6) binds k but its indicator uses j. → Count each observation using the bound index.; reason: The definition of an empirical cdf and (1) on p. 465 fix this index typo; no sample or rate is excluded.
--   - generalization: Almost-sure convergence of conditional samples as n grows, without specifying the coupling between sample sizes. → The conclusion holds for every common probability space carrying rows with the actual conditional vector laws.; reason: This includes the nested iid/order-statistic coupling; the distribution-free exponential empirical-cdf bound makes exceptional probabilities summable for every coupling. No case of the source is excluded.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, DOI 10.1287/msom.2014.0490, p. 471, THEOREM 2, PDF 8

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_Supplement_EmpiricalCdf

namespace NHPPArrivals.LinearRate.Supplement

open MeasureTheory Filter Topology

theorem empirical_cdf_limit {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (lam : ℝ → ℝ) (T c : ℝ) (hrate : AdmissibleRate lam T) (hc : 0 < c)
    (N : ℝ → Ω → ℕ) (X : ℕ → Ω → ℝ)
    (hN : IsNHPP P (fun s => c * lam s) T N X)
    (Y : (n : ℕ) → Ξ → Fin n → ℝ) (hY : ConditionalRows P N X T Q Y) :
    ∀ᵐ ξ ∂Q, Tendsto
      (fun n : ℕ => uniformError (empiricalCdf (Y n ξ)) (condCdf lam T))
      atTop (𝓝 0) := by sorry

end NHPPArrivals.LinearRate.Supplement
