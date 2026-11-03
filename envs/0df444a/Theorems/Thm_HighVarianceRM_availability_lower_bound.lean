-- Prove2me | Theorems.Thm_HighVarianceRM_availability_lower_bound
-- name    : HighVarianceRM.availability_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:40.265795+00:00
-- url     : https://prove2.me/theorems/a7c945c2-67f7-4f85-9a40-bb3bec8ed34a
-- title:
--   Proof of Theorem 5.1, first display: lower bound on the availability probability
-- statement:
--   Let $(\Omega,\mathbb P)$ carry a realization of the approximate policy with parameter $\theta\in[0,1]$ and a feasible solution $y$ of the Universal Fluid. For every period $t$ and every product $j$,
--
--   $$
--   \begin{aligned}
--   \mathbb P\{G_{jt}=1\}&\ge\mathbb P\Big\{\sum_{k=1}^T N_{ik}<c_i\ \ \forall i\in A_j\Big\}=1-\mathbb P\Big\{\exists i\in A_j:\ \sum_{k=1}^T N_{ik}\ge c_i\Big\}\\
--   &\ge1-\sum_{i\in A_j}\mathbb P\Big\{\sum_{k=1}^T N_{ik}\ge c_i\Big\}\ge1-L\exp\Big(-\frac{\tfrac32(1-\theta)^2c_{\min}}{2\theta+1}\Big)\ge1-L\exp\Big(-\frac{(1-\theta)^2c_{\min}}{2}\Big).
--   \end{aligned}
--   $$
--
--   With the tuning parameter of Theorem 5.1 the right end equals $1-L/c_{\min}$, which is the bound on $\mathbb P\{G_{jt}=1\}$ that the theorem needs.
--
--   **Formalization Note** The five links of the chain are the five conjuncts of the statement. $N_{ik}$ is the demand indicator of the run.
--
--   Differences from the source:
--   - generalization: y* an optimal solution of the Universal Fluid → y any feasible solution; reason: optimal solutions are feasible, and only feasibility is used; specializes to the source
--   - generalization: θ ∈ (0,1) → θ ∈ [0,1]; reason: the printed θ equals 1 at c_min = 1; every θ ∈ (0,1) is covered, so this specializes to the source
--   - generalization: the number of customers, the products of interest and the availability decisions are all independent → independence of the period slices (P_t, A_·t), of P_t from A_·t within a period, and of D from all slices (the fields of PolicyRun); reason: every fully independent family is such a run; A_jt for different j in one period may also be correlated
--   - reading: capacities c_i with no stated type → c_i a natural number; reason: the state space is Z₊^{|L|} (pp. 10, 18) and the dynamic program moves it by unit vectors from c
--   - encoding: at λ_jt = 0 the availability probability θ y*_jt/λ_jt is 0/0 → Lean's 0/0 = 0; reason: then y*_jt = 0 by feasibility and the product is never requested at t
--   - encoding: min_{i∈L} c_i with L unspecified → Nonempty R; reason: the minimum over an empty set is undefined; this excludes only that case
--   - encoding: time periods t = 1, …, T and D with values in {1, …, T} → periods t : Fin T, 0-based (the paper's t is t + 1), and D ω + 1 customers with D ω : Fin T; reason: an index shift; it changes no instance
--   - reading: a customer arrives at each period, and with probability λ_jt is interested in product j → Σ_j λ_jt = 1 for every t (field lam_sum of Instance); reason: p. 6: "there is a customer arrival at each time period with probability one" and "each customer arrives with the intention of purchasing a fixed product"; the dynamic program of p. 6 is an expectation only under it
-- source:
--   Bai et al., Fluid Approximations for Revenue Management under High-Variance Demand, Management Science, proof of Theorem 5.1, first display, p.23

import Mathlib
import Definitions.Def_HighVarianceRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace HighVarianceRM

/-- **Lower bound on the availability probability.** Bai et al., *Fluid Approximations for Revenue
Management under High-Variance Demand*, Management Science, doi:10.1287/mnsc.2023.4769, proof of
Theorem 5.1, first display, p. 23, the whole chain:
`P{G_jt = 1} ≥ P{∑_k N_ik < c_i ∀ i ∈ A_j} = 1 - P{∃ i ∈ A_j, ∑_k N_ik ≥ c_i}
≥ 1 - ∑_{i ∈ A_j} P{∑_k N_ik ≥ c_i} ≥ 1 - L exp(-(3/2)(1 - θ)² c_min / (2θ + 1))
≥ 1 - L exp(-(1 - θ)² c_min / 2)`.

**Formalization Note** The links are the five conjuncts, in the printed order; the last two compare
the bounds. `N` is the demand indicator of the run. `θ` ranges over `[0, 1]` (the paper: `(0, 1)`)
and `y` over feasible solutions (the paper: an optimal one). -/
theorem availability_lower_bound {R J : Type*} [Fintype R] [Nonempty R] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J] {T : ℕ} (I : Instance R J T) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {y : Fin T → J → ℝ} (hy : I.Feasible y) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (run : PolicyRun I θ y P)
    (t : Fin T) (j : J) :
    P.real {ω | ∀ i ∈ I.A j, ∑ k, run.N i k ω < I.c i} ≤ P.real {ω | run.G t j ω} ∧
    P.real {ω | ∀ i ∈ I.A j, ∑ k, run.N i k ω < I.c i} =
      1 - P.real {ω | ∃ i ∈ I.A j, I.c i ≤ ∑ k, run.N i k ω} ∧
    1 - ∑ i ∈ I.A j, P.real {ω | I.c i ≤ ∑ k, run.N i k ω} ≤
      1 - P.real {ω | ∃ i ∈ I.A j, I.c i ≤ ∑ k, run.N i k ω} ∧
    1 - I.L * Real.exp (-((3 / 2) * (1 - θ) ^ 2 * I.cmin / (2 * θ + 1))) ≤
      1 - ∑ i ∈ I.A j, P.real {ω | I.c i ≤ ∑ k, run.N i k ω} ∧
    1 - I.L * Real.exp (-((1 - θ) ^ 2 * I.cmin / 2)) ≤
      1 - I.L * Real.exp (-((3 / 2) * (1 - θ) ^ 2 * I.cmin / (2 * θ + 1))) := by sorry

end HighVarianceRM
