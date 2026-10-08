-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem51a
-- name    : NegativeDP.Stationary.theorem51a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:36.3165+00:00
-- url     : https://prove2.me/theorems/b9fa92a3-e871-4e1d-8d73-3fd6755859a9
-- title:
--   Theorem 5.1 (a) (N) — the operator T is monotone
-- statement:
--   In the negative dynamic programming problem, let $f:S\to A$ be a Borel rule and $T$ its operator, $Tu(s)=\int r(s,f(s),t)+u(t)\,dq(t\mid s,f(s))$. For $u,v\in M(S)$,
--
--   $$u\le v\ \Longrightarrow\ Tu\le Tv .$$
--
--   The paper states Theorem 5.1 for the discounted, positive and negative cases; this item is the negative case ($\beta=1$, $M(S)$ the non-positive extended-real Borel functions). Monotonicity is used in the proof of Theorem 8.3.
--
--   **Formalization Note.** $T$ is computed as $-\int(-r-u)\,dq$ in $[0,\infty]$; $u,v\in M(S)$ are hypotheses.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.1 (a)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 5.1 (a), case N (p. 879): `T` is monotone on `M(S)`. -/
theorem theorem51a (P : Problem S A) (f : {g : S → A // Measurable g}) (u v : S → EReal)
    (hu : IsNegM u) (hv : IsNegM v) (huv : u ≤ v) :
    T P f u ≤ T P f v := by sorry

end NegativeDP.Stationary
