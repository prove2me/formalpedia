-- Prove2me | Theorems.Thm_IPMJumpLB_rank_drop
-- name    : IPMJumpLB.rank_drop
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:32.97683+00:00
-- url     : https://prove2.me/theorems/23394391-b83f-4bb2-915f-1961bc6246a4
-- title:
--   Proof of Theorem 4.1 — one jump lowers the rank by at most $2\lceil 12bk^2/\eta\rceil$
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$, $\eta = \alpha \hat n_k$ and $h = \lceil 12bk^2/\eta\rceil$. For every jump from an $\eta$-iterate $(x, s, f)$ to an $\eta$-iterate $(x', s', f')$ of the unit-demand instance of Section 4,
--   $$
--   r(f) - r(f') \le 2h .
--   $$
--
--   The indices that leave the rank set in a jump form a contiguous block of gadgets whose net forward flow turns positive; a block of more than $2h$ of them would make the middle gadget violate both jump conditions.
--
--   **Formalization Note** The difference of ranks is taken in $\mathbb Z$.
--
--   Differences from the source:
--   - generalization: the paper states r(ℓ) − r(ℓ+1) ≤ 2h for consecutive iterates of a path-following sequence → every jump between η-iterates; reason: each consecutive pair of a path-following sequence is such a jump
--   - encoding: b, η, h as fixed values → variables with defining hypotheses; rank difference in ℤ; reason: same instances, no truncated subtraction
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.14 ("Thus r(ℓ) − r(ℓ+1) ≤ 2h")

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
import Definitions.Def_IPMJumpLB_IsJump
import Definitions.Def_IPMJumpLB_shortcutOutFlow
import Definitions.Def_IPMJumpLB_rank

namespace IPMJumpLB

/-- The rank drops by at most `2h` in one jump (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.14): with
`h = ⌈12bk²/η⌉`, every jump `p → q` between η-iterates of the Section 4 instance satisfies
`r(p) − r(q) ≤ 2h`. -/
theorem rank_drop (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ))
    (h : ℕ) (hh : h = ⌈12 * (b : ℝ) * (k : ℝ) ^ 2 / η⌉₊)
    (p q : (VertexU b k → ℝ) × (ArcU b k → ℝ)) (hpq : IsJump (unitSSSP b k) η p q) :
    (rank b k p.2 : ℤ) - rank b k q.2 ≤ 2 * h := by sorry

end IPMJumpLB
