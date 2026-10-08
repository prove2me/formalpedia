-- Prove2me | Theorems.Thm_HordijkKallenbergLP_ExtremePoint_theorem_10
-- name    : HordijkKallenbergLP.ExtremePoint.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:58:12.823582+00:00
-- url     : https://prove2.me/theorems/b8448d20-9e0a-49f5-bc10-83397871d86c
-- title:
--   Theorem 10 — the representative (x(f), y(f)) of a pure stationary policy is an extreme point of the dual LP
-- statement:
--   Consider a Markov decision chain with finite state space $E$, finite nonempty action sets $A(i)$ and transition probabilities $p_{iaj}$, and weights $\beta_j>0$ with $\sum_j\beta_j=1$. Let $f^\infty$ be a pure stationary policy, $f(i)\in A(i)$, and let $(x(f),y(f))$ be its representative (6):
--   $$
--   x_{ia}(f)=[\beta^TP^*(f)]_i\,\delta_{a f(i)},\qquad y_{ia}(f)=[\beta^TD(f)+\gamma^TP^*(f)]_i\,\delta_{af(i)}.
--   $$
--   **Theorem 10.** The representative $(x(f),y(f))$ is an extreme point of the feasible set of the dual linear program (3)–(5):
--   $$
--   (x(f),y(f))\in\operatorname{ext}\{(x,y)\ :\ (3),(4),(5)\}.
--   $$
--
--   Under the correspondence of §3.3 between stationary policies and representatives, Theorem 10 places every pure stationary policy at a vertex of the dual feasible polyhedron. The paper remarks (p. 362, with an example in its reference [9]) that the converse fails: an extreme point may induce a non-pure policy.
--
--   **Formalization Note.** Being an extreme point includes feasibility. The variables are indexed by admissible pairs only. The vector $\gamma$ uses the denominator $\sum_{k\in E_j}p^*_{ki}$ in place of the printed $\sum_k p^*_{ki}$, a misprint under which the representative need not be feasible.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 361, Theorem 10

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

namespace HordijkKallenbergLP.ExtremePoint

/-- **Theorem 10.** Let `f^∞` be a pure and stationary policy. Then the corresponding
representative `(x(f), y(f))` is an extreme point of the dual linear programming problem.

Here `E` is finite, every `A(i)` is finite and nonempty, `β_j > 0` with `∑_j β_j = 1` (§2.1,
p. 353), the dual feasible set is (3)–(5) of p. 357, and `(x(f), y(f))` is (6) of p. 359 for the
rule `π_ia = 1` if `a = f(i)`, `0` otherwise.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 361, Theorem 10.

**Formalization Note.** Being an extreme point (`Set.extremePoints ℝ`) includes being feasible.
The LP variables are indexed by admissible pairs only (`Pair M`), so non-admissible coordinates
are absent rather than free. `γ` in (6) uses the denominator `∑_{k ∈ E_j} p*_ki` in place of the
printed `∑_k p*_ki` (a misprint: with it the representative need not be feasible; see `gamma`). -/
theorem theorem_10 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A) (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    (repX M β (pureRule f), repY M β (pureRule f)) ∈
      Set.extremePoints ℝ (dualFeasible M β) := by sorry

end HordijkKallenbergLP.ExtremePoint
