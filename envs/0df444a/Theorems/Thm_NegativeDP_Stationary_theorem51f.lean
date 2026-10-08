-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem51f
-- name    : NegativeDP.Stationary.theorem51f
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:58.194808+00:00
-- url     : https://prove2.me/theorems/4788bc8d-3df2-4d15-ad11-c36e12164641
-- title:
--   Theorem 5.1 (f) (N) — TI(π) = I(f, π), and TI(f^(∞)) = I(f^(∞)) = lim Tⁿ0
-- statement:
--   In the negative dynamic programming problem, let $f:S\to A$ be a Borel rule and $T$ its operator. For any policy $\pi=(\pi_1,\pi_2,\dots)$ let $(f,\pi)=(f,\pi_1,\pi_2,\dots)$ be the policy that uses $f$ at the first stage and then runs $\pi$ from the resulting state. Then
--
--   $$TI(\pi)=I(f,\pi),$$
--
--   and in particular, for the stationary policy $f^{(\infty)}$,
--
--   $$TI(f^{(\infty)})=I(f^{(\infty)})=\lim_{n\to\infty}T^n0 .$$
--
--   The return of $f^{(\infty)}$ is thus a fixed point of $T$ and is obtained by iterating $T$ from $0$. The paper states Theorem 5.1 for the discounted, positive and negative cases; this item is the negative case. Theorem 8.3 uses both identities.
--
--   **Formalization Note.** $(f,\pi)$ applies $\pi$'s $k$th kernel to the history with its first state–action pair removed. $I(\pi)$ for a general history-dependent $\pi$ is applied to $T$ without a separate measurability hypothesis: $T$ is a lower Lebesgue integral, defined for every function. The limit is pointwise in $[-\infty,0]$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.1 (f)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 5.1 (f), case N (p. 879): `TI(π) = I(f, π)` for every policy `π`, and in
particular `TI(f^(∞)) = I(f^(∞)) = lim_{n→∞} Tⁿ0`. -/
theorem theorem51f (P : Problem S A) (f : {g : S → A // Measurable g}) :
    (∀ π : Plan (S := S) (A := A), T P f (I P π) = I P (prefixPlan f π)) ∧
    T P f (I P (MarkovPlan.toPlan (stationary f))) = I P (MarkovPlan.toPlan (stationary f)) ∧
    ∀ s, Tendsto (fun n => (T P f)^[n] 0 s) atTop
      (𝓝 (I P (MarkovPlan.toPlan (stationary f)) s)) := by sorry

end NegativeDP.Stationary
