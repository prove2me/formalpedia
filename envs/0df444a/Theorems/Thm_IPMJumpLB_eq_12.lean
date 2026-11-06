-- Prove2me | Theorems.Thm_IPMJumpLB_eq_12
-- name    : IPMJumpLB.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:00.839617+00:00
-- url     : https://prove2.me/theorems/ead18416-e9d2-477d-9a54-f350d620a5c6
-- title:
--   Eq. (12) — decomposition of the duality gap of the unit-demand instance
-- statement:
--   For a potential $x$ with slacks $s = c - Bx$ and a flow $f$ on the unit-demand instance of Section 4, write $\Delta_i(x) = x_{v_i} - x_{v_{i+1}}$. The duality gap decomposes as
--   $$
--   D = \Bigl(2k - \sum_{i=0}^{k-1} \Delta_i(x)\Bigr) F_{S,\mathrm{out}} + D_{S,\mathrm{dem}} + D_P + D_L . \tag{12}
--   $$
--   On each shortcut path, $s_{(v_0,a_j)} f_{(v_0,a_j)} + s_{(a_j,v_k)} f_{(a_j,v_k)}$ splits into the flow continuing to $v_k$ times the total slack $2k - \sum_i \Delta_i(x)$ of the path, plus the unit absorbed at $a_j$.
--
--   Equation (12) is the replacement of (8) in the proof of Theorem 3.1 and is the starting point of all gap estimates in the proof of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: the paper states (12) at each iterate ℓ of a path-following sequence, with b = ⌈6/α⌉ and k ≥ 3 → every potential x and every arc vector f, for all b, k ∈ ℕ, with D_S,dem in its defining form Σ_j s_(v₀,a_j)(f_(v₀,a_j) − f_(a_j,v_k)); reason: with the defining form of D_S,dem the identity is algebraic, and it specializes to every iterate
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, Eq. (12), p.13

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack
import Definitions.Def_IPMJumpLB_gap
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat
import Definitions.Def_IPMJumpLB_unitSSSP
import Definitions.Def_IPMJumpLB_shortcutOutFlow
import Definitions.Def_IPMJumpLB_shortcutDemGap
import Definitions.Def_IPMJumpLB_pathGap
import Definitions.Def_IPMJumpLB_leafGap

namespace IPMJumpLB

/-- Eq. (12) (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.13): the duality gap of the Section 4 instance
decomposes as
`D = (2k − ∑_(i=0)^(k−1) Δᵢ(x)) F_S,out + D_S,dem + D_P + D_L`, where
`Δᵢ(x) = x_(vᵢ) − x_(vᵢ₊₁)`.

**Formalization Note** With `D_S,dem` in its defining form `∑_j s_(v₀,a_j)(f_(v₀,a_j) − f_(a_j,v_k))`
the identity holds for every potential `x` and every arc vector `f`, and for every `b, k`. -/
theorem eq_12 (b k : ℕ) (x : VertexU b k → ℝ) (f : ArcU b k → ℝ) :
    gap (unitSSSP b k) x f =
      (2 * (k : ℝ) - ∑ i : Fin k, (x (.path i.castSucc) - x (.path i.succ))) *
          shortcutOutFlow b k f +
        shortcutDemGap b k x f + pathGap b k x f + leafGap b k x f := by sorry

end IPMJumpLB
