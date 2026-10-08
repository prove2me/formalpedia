-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem41
-- name    : NegativeDP.Stationary.theorem41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:34.408981+00:00
-- url     : https://prove2.me/theorems/b19b928c-60e2-4e86-a67d-a2408c580551
-- title:
--   Theorem 4.1 (N) — random semi-Markov and random Markov policies with the same returns, for every return function
-- statement:
--   Let $S$, $A$ and the law of motion $q$ be fixed, let $\pi$ be any policy and $p$ a probability measure on $S$. Then there exist a random semi-Markov policy $\pi^*$ and a random Markov policy $\pi^{**}$ such that, **for every return function** $r$ (every non-positive Borel $r$ with $qr>-\infty$),
--
--   $$I(\pi)=I(\pi^*)\quad\text{at every state},\qquad pI(\pi)=pI(\pi^{**}).$$
--
--   The policies $\pi^*,\pi^{**}$ are chosen before the return function: they depend on $\pi$, $q$ and $p$ only. The theorem says that, without loss in expected return, one need only remember the initial state and the current state, and, if the initial state is drawn from a known $p$, only the current state.
--
--   The paper states Theorem 4.1 for the discounted, positive and negative cases; this item is the negative case.
--
--   **Formalization Note.** "For every return function $r$" is expressed by quantifying over every negative problem with the same law of motion as the given one, after the existential choice of $\pi^*,\pi^{**}$. $pI=\int I\,dp$ is computed as $-\int(-I)\,dp$ in $[0,\infty]$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 876, Theorem 4.1

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 4.1 (p. 876), negative case: for any policy `π` and `p ∈ P(S)` there are a random
semi-Markov `π*` and a random Markov `π**`, chosen before the return function, such that
`I(π) = I(π*)` and `pI(π) = pI(π**)` for every return function `r` (every negative problem
with the same law of motion). -/
theorem theorem41 (P : Problem S A) (π : Plan (S := S) (A := A))
    (p : Measure S) [IsProbabilityMeasure p] :
    ∃ π₁ π₂ : Plan (S := S) (A := A), IsRandomSemiMarkov π₁ ∧ IsRandomMarkov π₂ ∧
      ∀ P' : Problem S A, P'.q = P.q →
        (∀ s, I P' π s = I P' π₁ s) ∧ pInt p (I P' π) = pInt p (I P' π₂) := by sorry

end NegativeDP.Stationary
