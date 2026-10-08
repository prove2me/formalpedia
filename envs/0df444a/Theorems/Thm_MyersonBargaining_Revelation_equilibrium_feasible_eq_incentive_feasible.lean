-- Prove2me | Theorems.Thm_MyersonBargaining_Revelation_equilibrium_feasible_eq_incentive_feasible
-- name    : MyersonBargaining.Revelation.equilibrium_feasible_eq_incentive_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:46.907276+00:00
-- url     : https://prove2.me/theorems/bd85b57e-2882-47ae-8266-c88d96af5e72
-- title:
--   Theorem 2 — F** = F*: equilibrium-feasible and incentive-feasible allocations coincide
-- statement:
--   Let $(C,A_1,\dots,A_n,U_1,\dots,U_n,P)$ be a Bayesian collective choice problem. Let $F^*$ be the set of allocation vectors $V(\pi)$ of Bayesian incentive-compatible choice mechanisms on the standard response sets, and let $F^{**}$ be the set of allocation vectors $W(\pi,\sigma_1,\dots,\sigma_n)$ where $\pi$ is a choice mechanism on any nonempty finite response sets $S_1,\dots,S_n$ and $(\sigma_1,\dots,\sigma_n)$ is a response-plan equilibrium for $\pi$. Then
--
--   $$
--   F^{**}=F^*.
--   $$
--
--   For every response-plan equilibrium of every choice mechanism there is a Bayesian incentive-compatible direct mechanism giving every type of every player the same expected payoff, and conversely. So an arbitrator loses no generality by restricting to incentive-compatible mechanisms on the standard response sets.
--
--   **Formalization Note** $F^{**}$ quantifies over response sets $S:\iota\to$ `Type` with finite nonempty components; fixing $S_i=A_i$ would weaken the theorem. Both inclusions are stated.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 66, Theorem 2

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Model
import Definitions.Def_MyersonBargaining_Revelation_Equilibrium

namespace MyersonBargaining.Revelation

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

theorem equilibrium_feasible_eq_incentive_feasible (G : MyersonBargaining.NashSolution.Problem ι A C) :
    FStarStar G = MyersonBargaining.NashSolution.FStar G := by sorry

end MyersonBargaining.Revelation
