-- Prove2me | Theorems.Thm_IPMJumpLB_rank_endpoints
-- name    : IPMJumpLB.rank_endpoints
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:00.141192+00:00
-- url     : https://prove2.me/theorems/ee950aa0-1d35-4491-834e-c656a2ad7a59
-- title:
--   Proof of Theorem 4.1 — rank $k$ when $D \ge 6bk^3$, rank $0$ when $D \le k^3$
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$ and $\eta = \alpha \hat n_k$. For every $\eta$-iterate $(x, s, f)$ of the unit-demand instance of Section 4 with duality gap $D$,
--
--   1. if $D \ge 6bk^3$ then $r(f) = k$;
--   2. if $D \le k^3$ then $r(f) = 0$.
--
--   So a sequence starting with $D^{(0)} \ge 6bk^3$ and ending with $D^{(L)} \le k^3$ must lower the rank from $k$ to $0$.
--
--   Differences from the source:
--   - encoding: b = ⌈6/α⌉ and η = α n̂_k as fixed values → variables b, η with hypotheses b = ⌈6/α⌉₊ and η = α·n̂_k; reason: names for the paper's values, same instances
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.14 ("Again r(0) = k and r(L) = 0")

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
import Definitions.Def_IPMJumpLB_rank

namespace IPMJumpLB

/-- Rank at the endpoints (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.14): an η-iterate of the Section 4
instance with duality gap `D ≥ 6bk³` has rank `k`, and one with `D ≤ k³` has rank `0`. -/
theorem rank_endpoints (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ))
    (x : VertexU b k → ℝ) (f : ArcU b k → ℝ) (hit : IsEtaIterate (unitSSSP b k) η x f) :
    (6 * (b : ℝ) * (k : ℝ) ^ 3 ≤ gap (unitSSSP b k) x f → rank b k f = k) ∧
      (gap (unitSSSP b k) x f ≤ (k : ℝ) ^ 3 → rank b k f = 0) := by sorry

end IPMJumpLB
