-- Prove2me | Theorems.Thm_HighVarianceRM_approx_le_optimal
-- name    : HighVarianceRM.approx_le_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:55.123551+00:00
-- url     : https://prove2.me/theorems/45fb2ec4-c23c-41ba-b38c-d1d253f8a33c
-- title:
--   §5: the dynamic program dominates the approximate policy
-- statement:
--   For every parameter $\theta$, every $y$, and every realization of the approximate policy on a probability space,
--
--   $$
--   J_1(c)\ge J_{\mathrm{App}}(c).
--   $$
--
--   Here $J_1(c)$ is the value of the dynamic program and $J_{\mathrm{App}}(c)$ is the expectation of the revenue of the policy along a sample path. The statement relates a backward recursion to an expectation, and it is the first half of the chain in Theorem 5.1.
--
--   Differences from the source:
--   - generalization: the approximate policy built from an optimal y* with the tuning parameter θ → any θ and any y for which a run exists; reason: the argument uses only that the policy never sells without capacity; specializes to the source
--   - generalization: the number of customers, the products of interest and the availability decisions are all independent → independence of the period slices (P_t, A_·t), of P_t from A_·t within a period, and of D from all slices (the fields of PolicyRun); reason: every fully independent family is such a run; A_jt for different j in one period may also be correlated
--   - reading: capacities c_i with no stated type → c_i a natural number; reason: the state space is Z₊^{|L|} (pp. 10, 18) and the dynamic program moves it by unit vectors from c
--   - encoding: the §2 recursion with J_t = −∞ at negative capacity → the feasible-set form of eq. (1), p. 18, real-valued, with an explicit servability test; reason: the §2 recursion meets 0·(−∞) wherever ρ_t = 0, and the paper states that (1) is equivalent
--   - encoding: ρ_t = P{D ≥ t+1 | D ≥ t}, undefined at P{D ≥ t} = 0 → rho t = surv (t+1) / surv t, with Lean's 0/0 = 0; reason: J_t is then multiplied by ρ_{t−1} = 0, so the value is unaffected; the paper assumes the case away in Appendix A only (p. 20)
--   - encoding: at λ_jt = 0 the availability probability θ y*_jt/λ_jt is 0/0 → Lean's 0/0 = 0; reason: then y*_jt = 0 by feasibility and the product is never requested at t
--   - encoding: time periods t = 1, …, T and D with values in {1, …, T} → periods t : Fin T, 0-based (the paper's t is t + 1), and D ω + 1 customers with D ω : Fin T; reason: an index shift; it changes no instance
--   - reading: a customer arrives at each period, and with probability λ_jt is interested in product j → Σ_j λ_jt = 1 for every t (field lam_sum of Instance); reason: p. 6: "there is a customer arrival at each time period with probability one" and "each customer arrives with the intention of purchasing a fixed product"; the dynamic program of p. 6 is an expectation only under it
-- source:
--   Bai et al., Fluid Approximations for Revenue Management under High-Variance Demand, Management Science, §5, p.12; proof of Theorem 5.1, last sentence, p.23

import Mathlib
import Definitions.Def_HighVarianceRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace HighVarianceRM

/-- **The dynamic program dominates the approximate policy:** `J₁(c) ≥ J_App(c)`. Bai et al.,
*Fluid Approximations for Revenue Management under High-Variance Demand*, Management Science,
doi:10.1287/mnsc.2023.4769, §5, p. 12, and proof of Theorem 5.1, last sentence, p. 23.

**Formalization Note** `J1` is the value of the dynamic program, not a supremum over policies, so
this is a theorem relating a backward recursion to an expectation over a sample path. It holds for
every `θ` and `y`: a run only asks that its probabilities be probabilities. -/
theorem approx_le_optimal {R J : Type*} [Fintype R] [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {T : ℕ} (I : Instance R J T) {θ : ℝ} {y : Fin T → J → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I θ y P) :
    run.JApp ≤ I.J1 := by sorry

end HighVarianceRM
