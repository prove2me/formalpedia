-- Prove2me | Theorems.Thm_MyersonBargaining_Revelation_induced_isBIC
-- name    : MyersonBargaining.Revelation.induced_isBIC
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:26.159983+00:00
-- url     : https://prove2.me/theorems/b4bfdea1-c38d-4e2d-800c-8a1600480772
-- title:
--   Section 3, p. 67 — the equilibrium inequalities (14) for π imply the incentive-compatibility inequalities (6) for π′
-- statement:
--   Let $\pi$ be a choice mechanism on nonempty finite response sets $S_1,\dots,S_n$ for a Bayesian collective choice problem, and let $(\sigma_1,\dots,\sigma_n)$ be a response-plan equilibrium for $\pi$, i.e. response plans satisfying (14). Then the induced direct mechanism
--
--   $$
--   \pi'(c\mid\alpha)=\sum_{s}\pi(c\mid s)\prod_{i=1}^n\sigma_i(s_i\mid\alpha_i)
--   $$
--
--   is Bayesian incentive-compatible:
--
--   $$
--   Z_i(\pi',a_i\mid a_i)\ge Z_i(\pi',b_i\mid a_i)\qquad\text{for all } i,\ a_i\in A_i,\ b_i\in A_i.
--   $$
--
--   Together with $V(\pi')=W(\pi,\sigma)$ this shows $F^{**}\subseteq F^*$, the revelation-principle half of Theorem 2.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 67, Section 3, proof of Theorem 2

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Model
import Definitions.Def_MyersonBargaining_Revelation_Equilibrium

namespace MyersonBargaining.Revelation

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

theorem induced_isBIC (G : MyersonBargaining.NashSolution.Problem ι A C) {S : ι → Type} [∀ i, Fintype (S i)]
    [∀ i, Nonempty (S i)] (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ)
    (hπ : MyersonBargaining.NashSolution.IsChoiceMechanism π) (hσ : ∀ i, IsResponsePlan (σ i))
    (heq : IsResponsePlanEq G π σ) :
    MyersonBargaining.NashSolution.IsBIC G (induced π σ) := by sorry

end MyersonBargaining.Revelation
