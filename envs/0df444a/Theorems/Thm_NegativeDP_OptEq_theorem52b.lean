-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem52b
-- name    : NegativeDP.OptEq.theorem52b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:30.031955+00:00
-- url     : https://prove2.me/theorems/c7a4eddc-fdd9-4697-bf78-d800dbd02969
-- title:
--   Theorem 5.2(b) (N) — $U(u+c) = Uu + c$
-- statement:
--   Let $\pi$ be a Markov policy of a negative dynamic programming problem and $U$ its operator ($Uu=\sup_n T_n u$). For a real constant $c$ and a function $u$ such that both $u$ and $u+c$ belong to $M(S)$,
--   $$U(u+c) = Uu + c .$$
--
--   The paper states this for the discounted, positive and negative cases as $U(u+c) = Uu + \beta c$; in the negative case $\beta = 1$. This item is the negative case.
--
--   **Formalization Note** The paper's statement implicitly requires $u + c\in M(S)$ (the operators act on $M(S)$), i.e. $u+c\le 0$; we state it as the hypothesis `IsNegM (u + c)`. Values are in `EReal`, where $-\infty + c = -\infty$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.2(b)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Theorem 5.2(b), p. 879, negative case (`β = 1`): `U(u + c) = Uu + c`
for a real constant `c`, where `u` and `u + c` are both in `M(S)`. -/
theorem theorem52b (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) (c : ℝ)
    (hu : NegativeDP.Stationary.IsNegM u) (huc : NegativeDP.Stationary.IsNegM (fun t => u t + (c : EReal))) :
    ∀ s, U P π (fun t => u t + (c : EReal)) s = U P π u s + (c : EReal) := by sorry

end NegativeDP.OptEq
