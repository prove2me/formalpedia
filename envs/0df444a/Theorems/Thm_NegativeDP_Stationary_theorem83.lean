-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem83
-- name    : NegativeDP.Stationary.theorem83
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:44.630272+00:00
-- url     : https://prove2.me/theorems/6dde30e6-545b-414c-afc0-096299128bff
-- title:
--   Theorem 8.3 (N) — if an optimal policy exists, an optimal stationary policy exists
-- statement:
--   Consider the negative dynamic programming problem: non-empty Borel state and action sets $S$, $A$, a law of motion $q(\cdot\mid s,a)$, a Borel return $r\le 0$ with $qr>-\infty$, and no discounting. Let $v^*(s)=\sup_\pi I(\pi)(s)$ be the optimal return, the supremum over all randomized history-dependent policies. If there exists an optimal policy $\pi^*$, that is,
--
--   $$I(\pi^*)(s)\ \ge\ v^*(s)\qquad\text{for every } s\in S,$$
--
--   then there exists a Borel rule $f:S\to A$ whose stationary policy $f^{(\infty)}=(f,f,\dots)$ is optimal:
--
--   $$I(f^{(\infty)})(s)\ \ge\ v^*(s)\qquad\text{for every } s\in S.$$
--
--   The theorem is one of the main results of the paper: with non-positive rewards, whenever an optimal policy exists at all, one can be found that uses a single measurable decision rule at every stage. The paper states it for the negative case and recalls the discounted case as previously known; this item is the negative case.
--
--   **Formalization Note.** Optimality compares with every randomized history-dependent plan, not only Markov or stationary ones. Returns lie in $[-\infty,0]$ and are computed as minus lower Lebesgue integrals of losses, so a return of $-\infty$ is kept. A stationary policy is the Markov plan that uses the same measurable rule at every stage.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 886, Theorem 8.3

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 8.3, case N (p. 886): if there exists an optimal policy `π*` (optimal against every
randomized history-dependent policy), then there exists an optimal stationary policy `f^(∞)`. -/
theorem theorem83 (P : Problem S A) (h : ∃ π : Plan (S := S) (A := A), IsOptimal P π) :
    ∃ f : {g : S → A // Measurable g}, IsOptimal P (MarkovPlan.toPlan (stationary f)) := by sorry

end NegativeDP.Stationary
