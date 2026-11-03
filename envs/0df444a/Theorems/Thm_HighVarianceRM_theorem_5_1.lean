-- Prove2me | Theorems.Thm_HighVarianceRM_theorem_5_1
-- name    : HighVarianceRM.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:53.440623+00:00
-- url     : https://prove2.me/theorems/e9d91d7e-f2ee-41df-a7db-7821f265dadb
-- title:
--   Theorem 5.1 (Asymptotic Tightness)
-- statement:
--   Consider an instance with at least one resource and with $c_i\ge1$ for every resource $i$, and let $c_{\min}=\min_{i}c_i$ and $L=\max_{j}|A_j|$. The Universal Fluid has an optimal solution. For every optimal solution $y^*$, with objective value $Z^*_{\mathrm{LP}}$, and every realization of the approximate policy built from $y^*$ with tuning parameter $\theta=1-\sqrt{2\log c_{\min}/c_{\min}}$,
--
--   $$
--   J_1(c)\ge J_{\mathrm{App}}(c)\qquad\text{and}\qquad J_{\mathrm{App}}(c)\ge\Big(1-\sqrt{\frac{2\log c_{\min}}{c_{\min}}}-\frac{L}{c_{\min}}\Big)\,Z^*_{\mathrm{LP}}.
--   $$
--
--   For $Z^*_{\mathrm{LP}}>0$ this is the printed chain
--
--   $$
--   \frac{J_1(c)}{Z^*_{\mathrm{LP}}}\ge\frac{J_{\mathrm{App}}(c)}{Z^*_{\mathrm{LP}}}\ge1-\sqrt{\frac{2\log c_{\min}}{c_{\min}}}-\frac{L}{c_{\min}}.
--   $$
--
--   The theorem holds for an arbitrary law of the number of customers, with no assumption on demand scaling. Together with the upper bound $Z^*_{\mathrm{LP}}\ge J_1(c)$ (Theorem 4.1 of the paper, not part of this mission), it shows that the Universal Fluid is asymptotically tight as $c_{\min}$ grows.
--
--   **Formalization Note** The optimum is existentially asserted so that the second clause is not vacuous.
--
--   Differences from the source:
--   - encoding: L and the capacities unrestricted → Nonempty R and c_i ≥ 1; reason: the minimum over an empty set and log c_min / c_min at c_min = 0 are undefined; these exclude only undefined cases
--   - reading: capacities c_i with no stated type → c_i a natural number; reason: the state space is Z₊^{|L|} (pp. 10, 18) and the dynamic program moves it by unit vectors from c
--   - encoding: the §2 recursion with J_t = −∞ at negative capacity → the feasible-set form of eq. (1), p. 18, real-valued, with an explicit servability test; reason: the §2 recursion meets 0·(−∞) wherever ρ_t = 0, and the paper states that (1) is equivalent
--   - generalization: the ratios J_1/Z* and J_App/Z* → products with Z*; reason: equivalent for Z* > 0, and also covers Z* = 0, where the ratios are undefined
--   - generalization: θ ∈ (0,1) → the printed θ at every c_min ≥ 1, including θ = 1 at c_min = 1; reason: the formula leaves (0,1) only there, and the bound still holds
--   - generalization: f_j ≥ 0, tacit in the last display of the proof (p. 23) → any real f_j; reason: if f_j < 0 and P{D ≥ t} > 0 then optimality forces y*_jt = 0, so both sides of that term vanish; specializes to the source
--   - generalization: the number of customers, the products of interest and the availability decisions are all independent → independence of the period slices (P_t, A_·t), of P_t from A_·t within a period, and of D from all slices (the fields of PolicyRun); reason: every fully independent family is such a run; A_jt for different j in one period may also be correlated
--   - encoding: at λ_jt = 0 the availability probability θ y*_jt/λ_jt is 0/0 → Lean's 0/0 = 0; reason: then y*_jt = 0 by feasibility and the product is never requested at t
--   - encoding: ρ_t = P{D ≥ t+1 | D ≥ t}, undefined at P{D ≥ t} = 0 → rho t = surv (t+1) / surv t, with Lean's 0/0 = 0; reason: J_t is then multiplied by ρ_{t−1} = 0, so the value is unaffected; the paper assumes the case away in Appendix A only (p. 20)
--   - reading: A_jt drawn only when capacity is available (§5) → A_jt drawn at every period and capacity checked at the sale (App. B, p. 21); reason: the sales are identical, and the proof uses the variables of App. B
--   - reading: "letting y* be an optimal solution" → an optimal solution exists, and the bounds hold for every optimal solution and every realization of the policy; reason: the strongest reading; the existence clause keeps the statement from being vacuous
--   - encoding: time periods t = 1, …, T and D with values in {1, …, T} → periods t : Fin T, 0-based (the paper's t is t + 1), and D ω + 1 customers with D ω : Fin T; reason: an index shift; it changes no instance
--   - reading: a customer arrives at each period, and with probability λ_jt is interested in product j → Σ_j λ_jt = 1 for every t (field lam_sum of Instance); reason: p. 6: "there is a customer arrival at each time period with probability one" and "each customer arrives with the intention of purchasing a fixed product"; the dynamic program of p. 6 is an expectation only under it
-- source:
--   Bai et al., Fluid Approximations for Revenue Management under High-Variance Demand, Management Science, Theorem 5.1, p.12

import Mathlib
import Definitions.Def_HighVarianceRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace HighVarianceRM

/-- **Theorem 5.1 (Asymptotic Tightness).** Bai et al., *Fluid Approximations for Revenue Management
under High-Variance Demand*, Management Science, doi:10.1287/mnsc.2023.4769, Theorem 5.1, p. 12:
`J₁(c) / Z*_LP ≥ J_App(c) / Z*_LP ≥ 1 - √(2 log c_min / c_min) - L / c_min`.

The Universal Fluid has an optimal solution, and for every optimal solution `y` and every
realization of the approximate policy built from `y` with `θ = 1 - √(2 log c_min / c_min)`, both
inequalities hold.

**Formalization Note** The ratios are stated as products with `Z*_LP = I.objective y`: they are
equivalent for `Z*_LP > 0`, and in Lean a ratio at `Z*_LP = 0` would read `0`. `1 ≤ c_i` and
`Nonempty R` exclude only the undefined `log c_min / c_min` at `c_min = 0` and `min` over the empty
set. There is no sign hypothesis on `f` and no assumption on the law of `D`. -/
theorem theorem_5_1 {R J : Type*} [Fintype R] [Nonempty R] [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {T : ℕ} (I : Instance R J T) (hc : ∀ i, 1 ≤ I.c i) :
    (∃ y, I.IsOptimal y) ∧
      ∀ y, I.IsOptimal y →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (run : PolicyRun I I.theta y P),
          run.JApp ≤ I.J1 ∧
            (1 - Real.sqrt (2 * Real.log I.cmin / I.cmin) - I.L / I.cmin) * I.objective y ≤
              run.JApp := by sorry

end HighVarianceRM
