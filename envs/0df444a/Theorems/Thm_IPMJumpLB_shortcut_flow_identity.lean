-- Prove2me | Theorems.Thm_IPMJumpLB_shortcut_flow_identity
-- name    : IPMJumpLB.shortcut_flow_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:52.167558+00:00
-- url     : https://prove2.me/theorems/d864e281-ecd1-4115-9f9f-2ff2b1683f89
-- title:
--   Proof of Theorem 4.1 — leaf arcs carry one unit and $F_{S,\mathrm{in}} = F_{S,\mathrm{out}} + (b-2)k^2$
-- statement:
--   Let $f$ satisfy flow conservation on the unit-demand instance of Section 4. Since each leaf has demand $-1$ and a single incoming arc, every leaf arc carries exactly one unit; conservation at each shortcut vertex $a_j$ gives
--   $$
--   f_{(v_0, a_j)} = f_{(a_j, v_k)} + 1 ,
--   $$
--   and hence
--   $$
--   F_{S,\mathrm{in}} = F_{S,\mathrm{out}} + (b-2)k^2 .
--   $$
--
--   These identities let the proof of Theorem 4.1 track the two shortcut flows through a single quantity.
--
--   Differences from the source:
--   - generalization: the paper states the identities for the iterates of a path-following sequence, with b = ⌈6/α⌉ and k ≥ 3 → every vector f satisfying flow conservation on the instance, for all b, k ∈ ℕ; reason: only conservation is used, and every iterate satisfies it
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.11

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_IsFlowFeasible
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat
import Definitions.Def_IPMJumpLB_unitSSSP
import Definitions.Def_IPMJumpLB_shortcutInFlow
import Definitions.Def_IPMJumpLB_shortcutOutFlow

namespace IPMJumpLB

/-- Shortcut and leaf flows (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.11): every leaf arc carries exactly
one unit, conservation at `a_j` gives `f_(v₀, a_j) = f_(a_j, v_k) + 1`, and hence
`F_S,in = F_S,out + (b − 2)k²`.

**Formalization Note** Stated for every flow satisfying conservation on the instance with any
parameters `b, k` (the paper states it for the iterates of a sequence, with `b = ⌈6/α⌉`, `k ≥ 3`). -/
theorem shortcut_flow_identity (b k : ℕ) (f : ArcU b k → ℝ)
    (hf : IsFlowFeasible (unitSSSP b k) f) :
    (∀ i t, f (.leafArc i t) = 1) ∧ (∀ t, f (.extraLeafArc t) = 1) ∧
      (∀ j, f (.scIn j) = f (.scOut j) + 1) ∧
      shortcutInFlow b k f = shortcutOutFlow b k f + (((b - 2) * k ^ 2 : ℕ) : ℝ) := by sorry

end IPMJumpLB
