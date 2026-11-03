-- Prove2me | Theorems.Thm_HighVarianceRM_demand_dominates_capacity
-- name    : HighVarianceRM.demand_dominates_capacity
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:45.96213+00:00
-- url     : https://prove2.me/theorems/b51f619b-6439-45b6-b891-d836b6bcab79
-- title:
--   App. B, display before Lemma B.1: demand dominates capacity consumption
-- statement:
--   Let $(\Omega,\mathbb P)$ carry a realization of the approximate policy with parameter $\theta\in[0,1]$ and a feasible solution $y$ of the Universal Fluid, and let $N_{it}$ be the demand indicator of resource $i$ at period $t$. Then:
--
--   1. for every resource $i$, the variables $(N_{it})_{t}$ are independent, take values in $\{0,1\}$, and satisfy $\mathbb P\{N_{it}=1\}=\theta\sum_{j}\mathbf 1_{(i\in A_j)}\,y_{jt}$;
--   2. for every period $t$ and every product $j$,
--
--   $$
--   \mathbb P\Big\{\sum_{k=1}^T N_{ik}<c_i\ \ \forall i\in A_j\Big\}\le\mathbb P\{G_{jt}=1\}.
--   $$
--
--   Sales at a period depend on the remaining capacity and are not independent, whereas the demand indicators are independent, with an explicit law. The statement compares the two.
--
--   Differences from the source:
--   - generalization: y* an optimal solution of the Universal Fluid → y any feasible solution; reason: optimal solutions are feasible, and only feasibility is used; specializes to the source
--   - generalization: θ ∈ (0,1) → θ ∈ [0,1]; reason: the printed θ equals 1 at c_min = 1; every θ ∈ (0,1) is covered, so this specializes to the source
--   - generalization: the number of customers, the products of interest and the availability decisions are all independent → independence of the period slices (P_t, A_·t), of P_t from A_·t within a period, and of D from all slices (the fields of PolicyRun); reason: every fully independent family is such a run; A_jt for different j in one period may also be correlated
--   - reading: capacities c_i with no stated type → c_i a natural number; reason: the state space is Z₊^{|L|} (pp. 10, 18) and the dynamic program moves it by unit vectors from c
--   - encoding: at λ_jt = 0 the availability probability θ y*_jt/λ_jt is 0/0 → Lean's 0/0 = 0; reason: then y*_jt = 0 by feasibility and the product is never requested at t
--   - reading: "a collection of independent Bernoulli random variables" N_it → the demand indicator of the run, on the same probability space; reason: the paper uses N_it pathwise and jointly over the resources of a product (pp. 21–22), which needs this concrete variable; its law and independence become conclusions
--   - encoding: Bernoulli random variables → measurable ℕ-valued functions with values in {0,1}, measurability being part of the conclusion; reason: this is what a Bernoulli random variable is
--   - encoding: time periods t = 1, …, T and D with values in {1, …, T} → periods t : Fin T, 0-based (the paper's t is t + 1), and D ω + 1 customers with D ω : Fin T; reason: an index shift; it changes no instance
--   - reading: a customer arrives at each period, and with probability λ_jt is interested in product j → Σ_j λ_jt = 1 for every t (field lam_sum of Instance); reason: p. 6: "there is a customer arrival at each time period with probability one" and "each customer arrives with the intention of purchasing a fixed product"; the dynamic program of p. 6 is an expectation only under it
-- source:
--   Bai et al., Fluid Approximations for Revenue Management under High-Variance Demand, Management Science, App. B, display before Lemma B.1, p.22

import Mathlib
import Definitions.Def_HighVarianceRM_PolicyRun

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace HighVarianceRM

/-- **Demand dominates capacity consumption.** Bai et al., *Fluid Approximations for Revenue
Management under High-Variance Demand*, Management Science, doi:10.1287/mnsc.2023.4769, App. B,
display before Lemma B.1, p. 22.

For every resource `i`, the demand indicators `(N_it)_t` are measurable, independent and
`{0, 1}`-valued, with `P{N_it = 1} = θ ∑_j 1(i ∈ A_j) y_jt`; and for all `t`, `j`,
`P{∑_k N_ik < c_i ∀ i ∈ A_j} ≤ P{G_jt = 1}`.

**Formalization Note** The sum in the event runs over all `T` periods, as printed. `θ` ranges over
`[0, 1]` (the paper: `(0, 1)`) and `y` over feasible solutions (the paper: an optimal one).
Measurability is stated so that Lemma B.1 applies to `N`. -/
theorem demand_dominates_capacity {R J : Type*} [Fintype R] [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {T : ℕ} (I : Instance R J T) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {y : Fin T → J → ℝ} (hy : I.Feasible y) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (run : PolicyRun I θ y P) :
    (∀ i : R, (∀ t, Measurable (run.N i t)) ∧ iIndepFun (run.N i) P ∧
      (∀ t ω, run.N i t ω = 0 ∨ run.N i t ω = 1) ∧
      ∀ t, P.real {ω | run.N i t ω = 1} = θ * ∑ j, if i ∈ I.A j then y t j else 0) ∧
    ∀ (t : Fin T) (j : J),
      P.real {ω | ∀ i ∈ I.A j, ∑ k, run.N i k ω < I.c i} ≤ P.real {ω | run.G t j ω} := by sorry

end HighVarianceRM
