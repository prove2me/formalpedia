-- Prove2me | Theorems.Thm_IPMJumpLB_telescoping
-- name    : IPMJumpLB.telescoping
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:34.017742+00:00
-- url     : https://prove2.me/theorems/366f821b-df3a-48d0-b5d1-1b342e1eb7e1
-- title:
--   Proof of Theorem 4.1 — telescoping gives $k \le 2hL$, and $h \le 24bk^2/\eta$
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$, $\eta = \alpha \hat n_k$ and $h = \lceil 12bk^2/\eta\rceil$. Every $\eta$-path-following sequence of length $L$ on the unit-demand instance of Section 4 with $D^{(0)} \ge 6bk^3$ and $D^{(L)} \le k^3$ satisfies
--   $$
--   k \le 2hL .
--   $$
--   Moreover $\eta = \alpha \hat n_k \le 2bk^2$, and hence $h \le 24bk^2/\eta$.
--
--   Together these give the chain of lower bounds on $L$ in Theorem 4.1.
--
--   Differences from the source:
--   - encoding: b, η, h as fixed values → variables with defining hypotheses; k ≤ 2hL stated in ℕ; reason: same instances; the cast to ℝ is monotone
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.14 (last paragraph)

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
import Definitions.Def_IPMJumpLB_IsPathFollowing

namespace IPMJumpLB

/-- Telescoping and the final arithmetic (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.14): with
`h = ⌈12bk²/η⌉`, every η-path-following sequence of length `L` on the Section 4 instance with
`D⁽⁰⁾ ≥ 6bk³` and `D⁽ᴸ⁾ ≤ k³` satisfies `k ≤ 2hL`; moreover `η ≤ 2bk²` and `h ≤ 24bk²/η`. -/
theorem telescoping (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ))
    (h : ℕ) (hh : h = ⌈12 * (b : ℝ) * (k : ℝ) ^ 2 / η⌉₊)
    (L : ℕ) (seq : ℕ → (VertexU b k → ℝ) × (ArcU b k → ℝ))
    (hseq : IsPathFollowing (unitSSSP b k) η L seq)
    (h0 : 6 * (b : ℝ) * (k : ℝ) ^ 3 ≤ gap (unitSSSP b k) (seq 0).1 (seq 0).2)
    (hL : gap (unitSSSP b k) (seq L).1 (seq L).2 ≤ (k : ℝ) ^ 3) :
    k ≤ 2 * h * L ∧ η ≤ 2 * (b : ℝ) * (k : ℝ) ^ 2 ∧
      (h : ℝ) ≤ 24 * (b : ℝ) * (k : ℝ) ^ 2 / η := by sorry

end IPMJumpLB
