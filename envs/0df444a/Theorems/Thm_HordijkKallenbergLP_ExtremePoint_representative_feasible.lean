-- Prove2me | Theorems.Thm_HordijkKallenbergLP_ExtremePoint_representative_feasible
-- name    : HordijkKallenbergLP.ExtremePoint.representative_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:56:56.194268+00:00
-- url     : https://prove2.me/theorems/38da0bf1-d6ef-4fd5-8eb8-38a8c1b7fd5c
-- title:
--   §3.3, pp. 359–360 — the representative (x(π), y(π)) of a stationary policy is a feasible solution of the dual LP
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, and let $\pi$ be a stationary rule: $\pi_{ia}\ge 0$ for $a\in A(i)$ and $\sum_{a\in A(i)}\pi_{ia}=1$ for every state $i$. Then the representative $(x(\pi),y(\pi))$ defined by (6) is a feasible solution of the dual linear program:
--   $$
--   (x(\pi),y(\pi))\ \text{satisfies (3), (4) and (5)}.
--   $$
--
--   Feasibility of the representative is the first half of the correspondence between stationary policies and dual solutions of §3.3, and it is part of the conclusion of Theorem 10.
--
--   **Formalization Note.** The vector $\gamma$ in (6) uses the denominator $\sum_{k\in E_j}p^*_{ki}(\pi)$; with the printed $\sum_k p^*_{ki}(\pi)$ the representative is in general not nonnegative.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, pp. 359–360, §3.3, feasibility of (x(π), y(π))

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

namespace HordijkKallenbergLP.ExtremePoint

/-- **§3.3, pp. 359–360 (unnumbered): the representative is a feasible solution.** For every
stationary rule `π` (randomized, supported on the admissible actions) and every `β` with
`β_j > 0`, `∑_j β_j = 1`, the representative `(x(π), y(π))` of (6) satisfies the constraints
(3)–(5) of the dual linear program.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, pp. 359–360, §3.3
("First, we show that (x(π), y(π)) is a feasible solution.").

**Formalization Note.** `γ` in `repY` uses the denominator `∑_{k ∈ E_j} p*_ki` (see `gamma`):
with the printed `∑_k p*_ki` the claim fails when transient states feed an ergodic set. -/
theorem representative_feasible {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβpos : ∀ j, 0 < β j)
    (hβsum : ∑ j, β j = 1) (π : S → A → ℝ) (hπ : IsStationaryRule M π) :
    (repX M β π, repY M β π) ∈ dualFeasible M β := by sorry

end HordijkKallenbergLP.ExtremePoint
