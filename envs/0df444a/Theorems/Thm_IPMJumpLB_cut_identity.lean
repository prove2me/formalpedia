-- Prove2me | Theorems.Thm_IPMJumpLB_cut_identity
-- name    : IPMJumpLB.cut_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:07.923206+00:00
-- url     : https://prove2.me/theorems/de522f22-3faf-477c-9dd1-ebf642c86d49
-- title:
--   Proof of Theorem 4.1 — the cut identity $f_{e_i^+} - f_{e_i^-} = 2k^2 - ki - F_{S,\mathrm{out}}$
-- statement:
--   Let $f$ satisfy flow conservation on the unit-demand instance of Section 4 and let $0 \le i < k$. Summing conservation over the cut $U_i$, made of $v_0, \dots, v_i$ and the $i(k-1)$ leaves attached to $v_1, \dots, v_i$ (net supply $bk^2 - ki$), gives
--   $$
--   f_{e_i^+} - f_{e_i^-} + F_{S,\mathrm{in}} = bk^2 - ki ,
--   $$
--   and substituting $F_{S,\mathrm{in}} = F_{S,\mathrm{out}} + (b-2)k^2$,
--   $$
--   f_{e_i^+} - f_{e_i^-} = 2k^2 - ki - F_{S,\mathrm{out}} .
--   $$
--
--   The net forward flow on gadget $i$ therefore changes sign exactly when the shortcut flow crosses $2k^2 - ki$; these values are $k$ apart.
--
--   Differences from the source:
--   - generalization: the paper states the identity for the iterates of a path-following sequence, with b = ⌈6/α⌉ and k ≥ 3 → every vector f satisfying flow conservation on the instance, every k ∈ ℕ and every b ≥ 2; reason: only conservation is used, and b = ⌈6/α⌉ ≥ 7
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.13

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

/-- The cut identity (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.13): for `0 ≤ i < k`, summing flow
conservation over the cut `Uᵢ = {v₀, …, vᵢ} ∪ {leaves of v₁, …, vᵢ}` gives
`f_(e⁺ᵢ) − f_(e⁻ᵢ) + F_S,in = bk² − ki`, and substituting `F_S,in = F_S,out + (b − 2)k²` gives
`f_(e⁺ᵢ) − f_(e⁻ᵢ) = 2k² − ki − F_S,out`.

**Formalization Note** Stated for every flow satisfying conservation, every `k` and every
`b ≥ 2` (the paper: iterates, `b = ⌈6/α⌉ ≥ 7`, `k ≥ 3`). -/
theorem cut_identity (b k : ℕ) (hb2 : 2 ≤ b) (f : ArcU b k → ℝ)
    (hf : IsFlowFeasible (unitSSSP b k) f) (i : Fin k) :
    f (.fwd i) - f (.bwd i) + shortcutInFlow b k f = (b : ℝ) * (k : ℝ) ^ 2 - (k : ℝ) * (i : ℕ) ∧
      f (.fwd i) - f (.bwd i) = 2 * (k : ℝ) ^ 2 - (k : ℝ) * (i : ℕ) - shortcutOutFlow b k f := by sorry

end IPMJumpLB
