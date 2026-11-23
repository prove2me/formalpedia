-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_Supplement_rejection_limits
-- name    : NHPPArrivals.LinearRate.Supplement.rejection_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:13:31.228259+00:00
-- url     : https://prove2.me/theorems/563722a3-6dd4-482b-83ff-fbd382862036
-- title:
--   THEOREM 6 — both asymptotic rejection probabilities for the exact CU KS test
-- statement:
--   Fix $T>0$, $a\ge0$, $b>0$, and $0<\alpha<1$. For each integer $n\ge1$ observe an NHPP of rate $n\lambda(t)=n(a+bt)$ on $[0,T]$. Divide the interval into $k_n\ge1$ equal subintervals and pool every arrival after rescaling it within its subinterval. Let $M_n=N_n(T)$ be the actual observed count, and let $R_n$ be the event that $M_n>0$ and the empirical uniform KS statistic of these $M_n$ pooled observations exceeds the exact critical value $\delta(M_n,\alpha)$. Then both implications hold:
--   $$\left(\frac{k_n}{\sqrt n}\to\infty\ \text{and}\ \frac n{k_n}\to\infty\right)\ \Longrightarrow\ P(R_n)\to\alpha,$$
--   $$\frac{k_n}{\sqrt n}\to0\ \Longrightarrow\ P(R_n)\to1.$$
--   Both $a=0$ and $a>0$ are included. In the second branch $k_n$ may stay bounded. The limit concerns a rejection probability with a random sample size, not just a population cdf discrepancy.
--
--   Differences from the source:
--   - reading: Theorem 6 concerns the NHPP test; its proof informally calls the sample size Kn. → The total M_n=N_n(T) is Poisson with mean nΛ(T), and the critical value is evaluated at M_n.; reason: The independent Poisson increment model determines the random total; Kn describes growth, not a deterministic-count hypothesis.
--   - encoding: The CU KS test uses the null critical value at the significance level. → The critical value is the exact null upper-tail quantile, for every fixed 0<alpha<1.; reason: This encodes the equality defining the test on p. 465 and avoids substituting its 0.05 approximation.
--   - encoding: The test is described for an observed sample. → At M_n=0 the test does not reject; at n=0 the sequence may be arbitrary.; reason: The empty event has probability exp(-nΛ(T)) tending to zero. Defaults do not affect either limit.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, DOI 10.1287/msom.2014.0490, p. 474, THEOREM 6, PDF 11

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_Supplement_KSTest

namespace NHPPArrivals.LinearRate.Supplement

open MeasureTheory Filter Topology

theorem rejection_limits {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (a b T : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hT : 0 < T)
    (N : ℕ → ℝ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hN : ∀ n : ℕ, 1 ≤ n →
      IsNHPP (P n) (fun s => (n : ℝ) * linRate a b s) T (N n) (X n))
    (k : ℕ → ℕ) (hk : ∀ n, 1 ≤ k n)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1) :
    ((Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt (n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) / (k n : ℝ)) atTop atTop) →
      Tendsto (fun n : ℕ => rejectionProbability (P n) (N n) (X n) T (k n) alpha)
        atTop (𝓝 alpha)) ∧
    (Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => rejectionProbability (P n) (N n) (X n) T (k n) alpha)
        atTop (𝓝 1)) := by sorry

end NHPPArrivals.LinearRate.Supplement
