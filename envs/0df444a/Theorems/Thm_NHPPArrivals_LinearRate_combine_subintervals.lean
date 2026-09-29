-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_combine_subintervals
-- name    : NHPPArrivals.LinearRate.combine_subintervals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:18:44.492025+00:00
-- url     : https://prove2.me/theorems/a3caeb1d-ff41-4335-bbe1-5b38464a5519
-- title:
--   LEMMA 1 (17) — combining k equal subintervals gives the conditional cdf Σ p_j F_j
-- statement:
--   Let $\lambda$ be an arrival rate function on $[0,T]$, $T > 0$, that is integrable on $[0,T]$, nonnegative, and strictly positive except at finitely many points, and let $\Lambda(t) = \int_0^t \lambda(s)\,ds$. Let $X$ be one arrival time, with density $\lambda(s)/\Lambda(T)$ on $[0,T]$. Divide $[0,T]$ into $k \ge 1$ subintervals of length $T/k$, and rescale $X$ within the subinterval that contains it: if $(j-1)T/k \le X < jT/k$, put $U = (X - (j-1)T/k)/(T/k)$, that is, $U$ is the fractional part of $kX/T$. Then:
--
--   1. the density $\lambda/\Lambda(T)$ defines a probability measure on $[0,T]$;
--   2. the weights $p_j = (\Lambda(jT/k) - \Lambda((j-1)T/k))/\Lambda(T)$, $1 \le j \le k$, are nonnegative and sum to $1$;
--   3. $U$ has the conditional cdf
--   $$\mathbb P(U \le t) = F(t) = \sum_{j=1}^k p_j F_j(t), \qquad 0 \le t \le 1,$$
--   where $F_j(t) = \Lambda_j(tT/k)/\Lambda_j(T/k)$ and $\Lambda_j(t) = \Lambda((j-1)T/k + t) - \Lambda((j-1)T/k)$.
--
--   So the combined, rescaled data of the $k$ subintervals are i.i.d. with a cdf that is a convex combination of the conditional cdfs of the individual subintervals. This is what reduces the degree of nonhomogeneity of the combined data to those of the pieces.
--
--   **Formalization Note** The paper's "i.i.d. random variables" statement comes from its THEOREM 1 (the NHPP conditioning property), which is not formalized: the lemma is stated for the law of a single arrival (density $\lambda/\Lambda(T)$ on $[0,T]$), and the i.i.d. structure is inherited from THEOREM 1. The rescaling to $[0,1]$ is `Int.fract (k * x / T)`; the right endpoint $x = T$ and the subinterval boundaries have probability zero. The paper's standing assumption of §3.2 ("integrable over the finite interval of interest and strictly positive except at a finite number of points") is encoded as interval integrability on $[0,T]$, nonnegativity on $[0,T]$, and finiteness of the zero set in $[0,T]$; it guarantees $\Lambda(T) > 0$ and $\Lambda_j(T/k) > 0$.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, p. 472, LEMMA 1, (17); standing assumption §3.2, p. 471

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

namespace NHPPArrivals.LinearRate

open MeasureTheory

theorem combine_subintervals (lam : ℝ → ℝ) (T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k)
    (hint : IntervalIntegrable lam volume 0 T) (hnn : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ lam s)
    (hfin : {s ∈ Set.Icc (0:ℝ) T | lam s = 0}.Finite) :
    IsProbabilityMeasure (arrivalLaw lam T) ∧
    (∀ j ∈ Finset.Icc 1 k, 0 ≤ weight lam T k j) ∧
    ∑ j ∈ Finset.Icc 1 k, weight lam T k j = 1 ∧
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      (arrivalLaw lam T).real {x | Int.fract ((k:ℝ) * x / T) ≤ t} = mixCdf lam T k t := by sorry

end NHPPArrivals.LinearRate
