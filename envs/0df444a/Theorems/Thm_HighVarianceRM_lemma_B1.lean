-- Prove2me | Theorems.Thm_HighVarianceRM_lemma_B1
-- name    : HighVarianceRM.lemma_B1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:01.339564+00:00
-- url     : https://prove2.me/theorems/1226abe6-eef8-4b18-bd69-70a995ecc1b9
-- title:
--   Lemma B.1: concentration of the demand for a resource
-- statement:
--   Let $y$ be feasible for the Universal Fluid, let $\theta\in[0,1]$, and let $i$ be a resource. If $(N_{t})_{t=1}^T$ are independent Bernoulli random variables with $\mathbb P\{N_t=1\}=\theta\sum_{j}\mathbf 1_{(i\in A_j)}\,y_{jt}$, then
--
--   $$
--   \mathbb P\Big\{\sum_{t=1}^T N_t\ge c_i\Big\}\le\exp\Big(-\frac{\tfrac32(1-\theta)^2c_{\min}}{2\theta+1}\Big).
--   $$
--
--   This is the concentration bound behind the guarantee of Theorem 5.1: it controls the probability that the demand for a resource reaches its capacity.
--
--   **Formalization Note** The event has $c_i$ and the bound has $c_{\min}$, as printed. The family is arbitrary, on any probability space.
--
--   Differences from the source:
--   - generalization: y* an optimal solution of the Universal Fluid → y any feasible solution; reason: optimal solutions are feasible, and only feasibility is used; specializes to the source
--   - generalization: θ ∈ (0,1) → θ ∈ [0,1]; reason: the printed θ equals 1 at c_min = 1; every θ ∈ (0,1) is covered, so this specializes to the source
--   - reading: capacities c_i with no stated type → c_i a natural number; reason: the state space is Z₊^{|L|} (pp. 10, 18) and the dynamic program moves it by unit vectors from c
--   - encoding: min_{i∈L} c_i with L unspecified → Nonempty R; reason: the minimum over an empty set is undefined; this excludes only that case
--   - encoding: Bernoulli random variables → measurable ℕ-valued functions with values in {0,1}; reason: this is what a Bernoulli random variable is
--   - encoding: time periods t = 1, …, T and D with values in {1, …, T} → periods t : Fin T, 0-based (the paper's t is t + 1), and D ω + 1 customers with D ω : Fin T; reason: an index shift; it changes no instance
--   - reading: a customer arrives at each period, and with probability λ_jt is interested in product j → Σ_j λ_jt = 1 for every t (field lam_sum of Instance); reason: p. 6: "there is a customer arrival at each time period with probability one" and "each customer arrives with the intention of purchasing a fixed product"; the dynamic program of p. 6 is an expectation only under it
-- source:
--   Bai et al., Fluid Approximations for Revenue Management under High-Variance Demand, Management Science, App. B, Lemma B.1, p.22

import Mathlib
import Definitions.Def_HighVarianceRM_Instance

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace HighVarianceRM

/-- **Lemma B.1.** Bai et al., *Fluid Approximations for Revenue Management under High-Variance
Demand*, Management Science, doi:10.1287/mnsc.2023.4769, App. B, Lemma B.1, p. 22.

If `(N t)_t` are independent Bernoulli random variables with
`P{N t = 1} = θ ∑_j 1(i ∈ A_j) y_jt`, then
`P{∑_t N t ≥ c_i} ≤ exp(-(3/2)(1 - θ)² c_min / (2θ + 1))`.

**Formalization Note** `N` is any such family on any probability space, as in the paper, encoded
as measurable `ℕ`-valued functions with values in `{0, 1}`. The event has `c_i`, the bound has
`c_min`. `y` is feasible (the paper: optimal; only the capacity constraint is used) and `θ ∈ [0, 1]`
(the paper: `(0, 1)`, but the printed `θ` equals `1` at `c_min = 1`). -/
theorem lemma_B1 {R J : Type*} [Fintype R] [Nonempty R] [Fintype J] {T : ℕ} (I : Instance R J T)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {y : Fin T → J → ℝ} (hy : I.Feasible y) (i : R)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Fin T → Ω → ℕ) (hNm : ∀ t, Measurable (N t)) (hind : iIndepFun N P)
    (hN01 : ∀ t ω, N t ω = 0 ∨ N t ω = 1)
    (hNp : ∀ t, P.real {ω | N t ω = 1} = θ * ∑ j, if i ∈ I.A j then y t j else 0) :
    P.real {ω | I.c i ≤ ∑ t, N t ω} ≤
      Real.exp (-((3 / 2) * (1 - θ) ^ 2 * I.cmin / (2 * θ + 1))) := by sorry

end HighVarianceRM
