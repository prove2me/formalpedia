-- Prove2me | Theorems.Thm_LeightonRao_BadExample_half_pairs_far
-- name    : LeightonRao.BadExample.half_pairs_far
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:52.849225+00:00
-- url     : https://prove2.me/theorems/bc10a8d5-3551-421e-9387-4a2ad57dbd95
-- title:
--   §2.1, p. 794 — in a 3-regular n-node graph at least half of the source–sink pairs are at distance ≥ ⌊log n⌋ − 2
-- statement:
--   Let $G$ be a 3-regular graph on $n\ge 8$ nodes and write $\log$ for $\log_2$. Then at least $n^2/2$ of the $n^2$ ordered pairs $(s,t)$ of nodes have graph distance
--   $$d_G(s,t)\ \ge\ \lfloor\log n\rfloor-2 .$$
--   In particular at least half of the $\binom n2$ commodities of the uniform multicommodity flow problem on $G$ have a shortest source–sink path with at least $\lfloor\log n\rfloor-2$ edges.
--
--   This is the step that forces every routing of the uniform flow on $G$ to use long paths.
--
--   **Formalization Note** Pairs are counted as ordered pairs over $V\times V$; a pair with $s=t$ has distance $0<\lfloor\log n\rfloor-2$ and is never counted, and $n^2/2$ ordered pairs give at least $\tfrac12\binom n2$ unordered ones. The paper's $\log n-2$ is stated with the floor $\lfloor\log n\rfloor-2$, which is what the ball bound yields (a printed slip for non-integer $\log n$). Distances are extended graph distances ($\infty$ across components).
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 794, §2.1, second paragraph after the min-cut display

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.BadExample

/-- §2.1, p. 794: in a 3-regular graph on `n ≥ 8` nodes, at least `n²/2` ordered pairs
`(s, t)` are at graph distance at least `⌊log₂ n⌋ − 2`. -/
theorem half_pairs_far {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (hn : 8 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 / 2 ≤
      ((Finset.univ.filter (fun p : V × V =>
        ((Nat.log 2 (Fintype.card V) - 2 : ℕ) : ℕ∞) ≤ G.edist p.1 p.2)).card : ℝ) := by sorry

end LeightonRao.BadExample
