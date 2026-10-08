-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem51bce
-- name    : NegativeDP.Stationary.theorem51bce
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:31.134858+00:00
-- url     : https://prove2.me/theorems/677191d8-1ab7-495c-a623-c7b361aa67e8
-- title:
--   Theorem 5.1 (b), (c), (e) (N) — T commutes with constants, T(sup uⱼ) ≥ sup Tuⱼ, and T is negative
-- statement:
--   In the negative dynamic programming problem ($\beta=1$), let $f:S\to A$ be a Borel rule and $T$ its operator. Then:
--
--   1. $T(u+c)=Tu+c$ for every real constant $c$, whenever $u$ and $u+c$ belong to $M(S)$;
--   2. $T(\sup_j u_j)\ge\sup_j Tu_j$ for every sequence $u_1,u_2,\dots$ in $M(S)$;
--   3. $u\le 0$ implies $Tu\le 0$ for $u\in M(S)$.
--
--   The paper states Theorem 5.1 for the discounted, positive and negative cases, with part (e) split by case; this item is the negative case, parts (b), (c) and (e N).
--
--   **Formalization Note.** The paper writes $T(u+c)=Tu+\beta c$ "for any constant $c$"; with $\beta=1$ and $M(S)$ the non-positive functions, we state it under the hypothesis that $u+c\in M(S)$ (for instance $c\le 0$), since $T$ is only defined on $M(S)$. The supremum in (c) is over a sequence, and $Tu$ is computed as $-\int(-r-u)\,dq$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.1 (b), (c), (e)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 5.1 (b), (c), (e) case N (p. 879), with `β = 1`:
(b) `T(u + c) = Tu + c` for a constant `c`, whenever `u` and `u + c` lie in `M(S)`;
(c) `T(sup_j u_j) ≥ sup_j Tu_j`;
(e) `u ≤ 0` implies `Tu ≤ 0`. -/
theorem theorem51bce (P : Problem S A) (f : {g : S → A // Measurable g}) :
    (∀ (u : S → EReal) (c : ℝ), IsNegM u → IsNegM (fun s => u s + c) →
      T P f (fun s => u s + c) = fun s => T P f u s + c) ∧
    (∀ uj : ℕ → S → EReal, (∀ j, IsNegM (uj j)) →
      ∀ s, (⨆ j, T P f (uj j) s) ≤ T P f (fun t => ⨆ j, uj j t) s) ∧
    (∀ u : S → EReal, IsNegM u → ∀ s, T P f u s ≤ 0) := by sorry

end NegativeDP.Stationary
