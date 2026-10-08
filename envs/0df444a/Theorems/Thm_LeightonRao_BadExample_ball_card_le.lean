-- Prove2me | Theorems.Thm_LeightonRao_BadExample_ball_card_le
-- name    : LeightonRao.BadExample.ball_card_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:35.19852+00:00
-- url     : https://prove2.me/theorems/7a24b552-36b3-403a-ba57-741a644babc9
-- title:
--   §2.1, p. 794 — in a 3-regular n-node graph at most n/2 nodes lie within distance ⌊log n⌋ − 3 of any node
-- statement:
--   Let $G$ be a 3-regular graph on $n\ge 8$ nodes and write $\log$ for $\log_2$. For every node $v$, the number of nodes $u$ whose graph distance from $v$ is at most $\lfloor\log n\rfloor-3$ satisfies
--   $$\bigl|\{u\in V:\ d_G(v,u)\le\lfloor\log n\rfloor-3\}\bigr|\ \le\ \frac n2 .$$
--
--   In the gap example this says that most nodes are far from any given node.
--
--   **Formalization Note** The paper writes $\log n-3$; the radius is the integer $\lfloor\log n\rfloor-3$ (for non-integer $\log n$ a graph distance is an integer anyway, so the ball is the same set as for radius $\log n-3$ rounded down). The hypothesis $n\ge 8$ makes $\lfloor\log n\rfloor\ge 3$, so the natural-number subtraction is exact. The distance is the extended graph distance (`SimpleGraph.edist`), which is $\infty$ between nodes in different components, so unreachable nodes are never counted as close.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 794, §2.1, second paragraph after the min-cut display

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.BadExample

/-- §2.1, p. 794: in a 3-regular graph on `n ≥ 8` nodes, at most `n/2` nodes lie within
graph distance `⌊log₂ n⌋ − 3` of any node `v`. -/
theorem ball_card_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (hn : 8 ≤ Fintype.card V) (v : V) :
    2 * ((Finset.univ.filter (fun u =>
        G.edist v u ≤ ((Nat.log 2 (Fintype.card V) - 3 : ℕ) : ℕ∞))).card : ℝ)
      ≤ (Fintype.card V : ℝ) := by sorry

end LeightonRao.BadExample
