-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem51d
-- name    : NegativeDP.Stationary.theorem51d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:42.198588+00:00
-- url     : https://prove2.me/theorems/206e56ae-672a-4767-985a-8659b1de17d4
-- title:
--   Theorem 5.1 (d) (N) — T is continuous along monotone sequences: uⱼ ↓ u gives Tuⱼ ↓ Tu, uⱼ ↑ u gives Tuⱼ ↑ Tu where sup Tuⱼ > −∞
-- statement:
--   In the negative dynamic programming problem, let $f:S\to A$ be a Borel rule and $T$ its operator. Let $u_1,u_2,\dots$ and $u$ belong to $M(S)$.
--
--   1. If $u_j\downarrow u$ pointwise, then $Tu_j\downarrow Tu$ pointwise.
--   2. If $u_j\uparrow u$ pointwise, then $Tu_j\uparrow Tu$ on the set $\{s:\ \sup_j Tu_j(s)>-\infty\}$.
--
--   The restriction in part 2 is necessary: if every $Tu_j(s)$ equals $-\infty$, the limit need not be $Tu(s)$. The paper states Theorem 5.1 for the discounted, positive and negative cases; this item is the negative case. Part 1 is used in the value-iteration results of §9.
--
--   **Formalization Note.** Convergence is in the order topology of $[-\infty,0]$; "$u_j\downarrow u$" is stated as an antitone sequence converging pointwise to $u$, and "$u_j\uparrow u$" as a monotone one.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.1 (d)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 5.1 (d), case N (p. 879): if `u_j ↓ u` then `Tu_j ↓ Tu`, and if `u_j ↑ u` then
`Tu_j ↑ Tu` on the set `{sup_j Tu_j > −∞}`; all functions in `M(S)`. -/
theorem theorem51d (P : Problem S A) (f : {g : S → A // Measurable g})
    (uj : ℕ → S → EReal) (u : S → EReal) (huj : ∀ j, IsNegM (uj j)) (hu : IsNegM u) :
    ((Antitone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
      ∀ s, Antitone (fun j => T P f (uj j) s) ∧
        Tendsto (fun j => T P f (uj j) s) atTop (𝓝 (T P f u s))) ∧
    ((Monotone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
      ∀ s, ⊥ < (⨆ j, T P f (uj j) s) →
        Monotone (fun j => T P f (uj j) s) ∧
          Tendsto (fun j => T P f (uj j) s) atTop (𝓝 (T P f u s))) := by sorry

end NegativeDP.Stationary
