-- Prove2me | Theorems.Thm_IPMJumpLB_endpoint_shortcut_flow
-- name    : IPMJumpLB.endpoint_shortcut_flow
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:10.317206+00:00
-- url     : https://prove2.me/theorems/4d009672-9828-4c2d-a20f-d50e306702bd
-- title:
--   Proof of Theorem 4.1 — $F_{S,\mathrm{out}} > 2k^2$ when $D \ge 6bk^3$, $F_{S,\mathrm{out}} < k^2$ when $D \le k^3$
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$ and $\eta = \alpha \hat n_k$. For every $\eta$-iterate $(x, s, f)$ of the unit-demand instance of Section 4 with duality gap $D$,
--
--   1. if $D \ge 6bk^3$ then $F_{S,\mathrm{out}} > 2k^2$;
--   2. if $D \le k^3$ then $F_{S,\mathrm{out}} < k^2$.
--
--   Applied to the first and last iterates of a sequence, these bounds place the shortcut flow above every flip value $2k^2 - ki$ at the start and below all of them at the end.
--
--   Differences from the source:
--   - encoding: b = ⌈6/α⌉ and η = α n̂_k as fixed values → variables b, η with hypotheses b = ⌈6/α⌉₊ and η = α·n̂_k; reason: names for the paper's values, same instances
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.13 ("At the endpoints we therefore have …")

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack
import Definitions.Def_IPMJumpLB_IsFlowFeasible
import Definitions.Def_IPMJumpLB_gap
import Definitions.Def_IPMJumpLB_IsEtaIterate
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat
import Definitions.Def_IPMJumpLB_unitSSSP
import Definitions.Def_IPMJumpLB_shortcutOutFlow

namespace IPMJumpLB

/-- Endpoint shortcut flows (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.13): an η-iterate of the Section 4
instance with duality gap `D ≥ 6bk³` has `F_S,out > 2k²`, and one with `D ≤ k³` has
`F_S,out < k²`. -/
theorem endpoint_shortcut_flow (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ))
    (x : VertexU b k → ℝ) (f : ArcU b k → ℝ) (hit : IsEtaIterate (unitSSSP b k) η x f) :
    (6 * (b : ℝ) * (k : ℝ) ^ 3 ≤ gap (unitSSSP b k) x f →
        2 * (k : ℝ) ^ 2 < shortcutOutFlow b k f) ∧
      (gap (unitSSSP b k) x f ≤ (k : ℝ) ^ 3 → shortcutOutFlow b k f < (k : ℝ) ^ 2) := by sorry

end IPMJumpLB
