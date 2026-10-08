-- Prove2me | Theorems.Thm_MyersonBargaining_Revelation_induced_V_eq_W
-- name    : MyersonBargaining.Revelation.induced_V_eq_W
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:20.7895+00:00
-- url     : https://prove2.me/theorems/2a8bf5a4-13c6-4163-a829-92200d7c11bb
-- title:
--   Section 3, p. 66 — the induced direct mechanism π′ generates the same allocation, V(π′) = W(π, σ)
-- statement:
--   Let $(C,A_1,\dots,A_n,U_1,\dots,U_n,P)$ be a Bayesian collective choice problem, let $\pi$ be a choice mechanism on nonempty finite response sets $S_1,\dots,S_n$, and let $\sigma_1,\dots,\sigma_n$ be response plans. Define the direct mechanism
--
--   $$
--   \pi'(c\mid\alpha)=\sum_{s\in S_1\times\cdots\times S_n}\pi(c\mid s)\prod_{i=1}^n\sigma_i(s_i\mid\alpha_i).
--   $$
--
--   Then $\pi'$ is a choice mechanism on the standard response sets $A_1,\dots,A_n$, and
--
--   $$
--   V(\pi')=W(\pi,\sigma_1,\dots,\sigma_n).
--   $$
--
--   Thus honest reporting under $\pi'$ gives every type of every player the same expected payoff as following the plans $\sigma$ under $\pi$. This is the first half of the proof of $F^{**}\subseteq F^*$ in Theorem 2.
--
--   **Formalization Note** The paper states this for a response-plan equilibrium $\sigma$; the identity uses only that the $\sigma_i$ are response plans, and the theorem is stated in that generality. The claim that $\pi'$ satisfies (2), implicit in the paper's "equivalent choice mechanism", is stated explicitly.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 66, Section 3, proof of Theorem 2

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Model
import Definitions.Def_MyersonBargaining_Revelation_Equilibrium

namespace MyersonBargaining.Revelation

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

theorem induced_V_eq_W (G : MyersonBargaining.NashSolution.Problem ι A C) {S : ι → Type} [∀ i, Fintype (S i)]
    [∀ i, Nonempty (S i)] (π : C → (∀ i, S i) → ℝ) (σ : ∀ i, S i → A i → ℝ)
    (hπ : MyersonBargaining.NashSolution.IsChoiceMechanism π) (hσ : ∀ i, IsResponsePlan (σ i)) :
    MyersonBargaining.NashSolution.IsChoiceMechanism (induced π σ) ∧ MyersonBargaining.NashSolution.V G (induced π σ) = W G π σ := by sorry

end MyersonBargaining.Revelation
