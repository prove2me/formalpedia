-- Prove2me | Theorems.Thm_MyersonBargaining_Revelation_honest_isResponsePlanEq
-- name    : MyersonBargaining.Revelation.honest_isResponsePlanEq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:40.550209+00:00
-- url     : https://prove2.me/theorems/d0f81fa1-8016-4f0a-87cf-35400008259a
-- title:
--   Section 3, p. 67 — the honest response plans form a response-plan equilibrium of an incentive-compatible mechanism
-- statement:
--   Let $\pi'$ be a Bayesian incentive-compatible choice mechanism on the standard response sets $A_1,\dots,A_n$ of a Bayesian collective choice problem. Define the honest response plans
--
--   $$
--   \sigma_i'(b_i\mid a_i)=\begin{cases}1&\text{if } b_i=a_i,\\0&\text{if } b_i\ne a_i.\end{cases}
--   $$
--
--   Then each $\sigma_i'$ is a response plan, $(\sigma_1',\dots,\sigma_n')$ is a response-plan equilibrium for $\pi'$ in the sense of (14), and the allocation it generates is the honest allocation:
--
--   $$
--   W(\pi',\sigma_1',\dots,\sigma_n')=V(\pi').
--   $$
--
--   This gives the inclusion $F^*\subseteq F^{**}$ of Theorem 2.
--
--   **Formalization Note** The paper states only the equilibrium property and then writes $x=V(\pi')=W(\pi',\sigma')$; both the response-plan property and the equality $W=V$ are made explicit conclusions. Deviations range over all, possibly mixed, response plans.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 67, Section 3, proof of Theorem 2

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Model
import Definitions.Def_MyersonBargaining_Revelation_Equilibrium

namespace MyersonBargaining.Revelation

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

theorem honest_isResponsePlanEq (G : MyersonBargaining.NashSolution.Problem ι A C) (π : C → (∀ i, A i) → ℝ)
    (hπ : MyersonBargaining.NashSolution.IsChoiceMechanism π) (hbic : MyersonBargaining.NashSolution.IsBIC G π) :
    (∀ i, IsResponsePlan (honest (A := A) i)) ∧
      IsResponsePlanEq G π (honest (A := A)) ∧ W G π (honest (A := A)) = MyersonBargaining.NashSolution.V G π := by sorry

end MyersonBargaining.Revelation
