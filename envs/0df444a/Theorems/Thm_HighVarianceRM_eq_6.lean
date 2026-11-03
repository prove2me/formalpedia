-- Prove2me | Theorems.Thm_HighVarianceRM_eq_6
-- name    : HighVarianceRM.eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:48.074542+00:00
-- url     : https://prove2.me/theorems/e1213d21-0214-4787-a8d1-28746729bde4
-- title:
--   Eq. (6): decomposition of the expected revenue of the approximate policy
-- statement:
--   Let $(\Omega,\mathbb P)$ carry a realization of the approximate policy with parameter $\theta\in[0,1]$ and a feasible solution $y$ of the Universal Fluid. Then the expected revenue factorizes period by period:
--
--   $$
--   J_{\mathrm{App}}(c)=\sum_{t=1}^T\sum_{j\in\mathcal J}f_j\,\mathbb P\{D\ge t\}\,\mathbb P\{A_{jt}=1\}\,\mathbb P\{\Lambda_{jt}=1\}\,\mathbb P\{G_{jt}=1\}
--   =\sum_{t=1}^T\sum_{j\in\mathcal J}f_j\,\mathbb P\{D\ge t\}\,\theta\,\frac{y_{jt}}{\lambda_{jt}}\,\lambda_{jt}\,\mathbb P\{G_{jt}=1\}.
--   $$
--
--   This identity reduces a lower bound on the revenue of the policy to a lower bound on the probabilities $\mathbb P\{G_{jt}=1\}$.
--
--   **Formalization Note** In the first sum every factor is the probability of an event of the run. In the second, $\mathbb P\{D\ge t\}$ is the instance's survival function `I.surv`.
--
--   Differences from the source:
--   - generalization: y* an optimal solution of the Universal Fluid → y any feasible solution; reason: optimal solutions are feasible, and only feasibility is used; specializes to the source
--   - generalization: θ ∈ (0,1) → θ ∈ [0,1]; reason: the printed θ equals 1 at c_min = 1; every θ ∈ (0,1) is covered, so this specializes to the source
--   - generalization: the number of customers, the products of interest and the availability decisions are all independent → independence of the period slices (P_t, A_·t), of P_t from A_·t within a period, and of D from all slices (the fields of PolicyRun); reason: every fully independent family is such a run; A_jt for different j in one period may also be correlated
--   - reading: capacities c_i with no stated type → c_i a natural number; reason: the state space is Z₊^{|L|} (pp. 10, 18) and the dynamic program moves it by unit vectors from c
--   - encoding: at λ_jt = 0 the availability probability θ y*_jt/λ_jt is 0/0 → Lean's 0/0 = 0; reason: then y*_jt = 0 by feasibility and the product is never requested at t
--   - encoding: time periods t = 1, …, T and D with values in {1, …, T} → periods t : Fin T, 0-based (the paper's t is t + 1), and D ω + 1 customers with D ω : Fin T; reason: an index shift; it changes no instance
--   - reading: a customer arrives at each period, and with probability λ_jt is interested in product j → Σ_j λ_jt = 1 for every t (field lam_sum of Instance); reason: p. 6: "there is a customer arrival at each time period with probability one" and "each customer arrives with the intention of purchasing a fixed product"; the dynamic program of p. 6 is an expectation only under it
-- source:
--   Bai et al., Fluid Approximations for Revenue Management under High-Variance Demand, Management Science, App. B, eq. (6), p.21

import Mathlib
import Definitions.Def_HighVarianceRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace HighVarianceRM

/-- **Eq. (6): decomposition of the expected revenue of the approximate policy.** Bai et al.,
*Fluid Approximations for Revenue Management under High-Variance Demand*, Management Science,
doi:10.1287/mnsc.2023.4769, App. B, eq. (6), p. 21.

**Formalization Note** The first equality carries the independence content; in it every factor is
the probability of an event of the run. `θ` ranges over `[0, 1]` (the paper: `(0, 1)`) and `y` over
feasible solutions (the paper: an optimal one). Period index 0-based. -/
theorem eq_6 {R J : Type*} [Fintype R] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] {T : ℕ}
    (I : Instance R J T) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {y : Fin T → J → ℝ}
    (hy : I.Feasible y) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I θ y P) :
    run.JApp = ∑ t : Fin T, ∑ j, I.f j * P.real {ω | t ≤ run.D ω} *
        P.real {ω | run.avail t j ω = true} * P.real {ω | run.req t ω = j} *
        P.real {ω | run.G t j ω} ∧
      run.JApp = ∑ t : Fin T, ∑ j, I.f j * I.surv t * (θ * (y t j / I.lam t j)) * I.lam t j *
        P.real {ω | run.G t j ω} := by sorry

end HighVarianceRM
