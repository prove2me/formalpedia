-- Prove2me | Theorems.Thm_IPMJumpLB_gap_term_bounds
-- name    : IPMJumpLB.gap_term_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:05.506715+00:00
-- url     : https://prove2.me/theorems/2870d481-4dcb-47db-a2e0-eb7b9726e2d9
-- title:
--   Proof of Theorem 4.1 — bounds on the gap terms of (12)
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$, $\eta = \alpha \hat n_k$ and $N_k = 2k^2 + k$. At every $\eta$-iterate $(x, s, f)$ of the unit-demand instance of Section 4,
--
--   1. $0 < D_{S,\mathrm{dem}} < 3(b-2)k^3$;
--   2. $\displaystyle D_P + D_L \le (2k^2 + k) D_{\max} \le \frac{N_k}{\eta} D \le \frac12 D$;
--   3. consequently
--   $$
--   \tfrac12 D < 3k F_{S,\mathrm{out}} + 3(b-2)k^3, \qquad k F_{S,\mathrm{out}} < D .
--   $$
--
--   These bounds tie the duality gap to the shortcut flow $F_{S,\mathrm{out}}$ up to constant factors.
--
--   **Formalization Note** $D_{\max}$ is the supremum of $s_e f_e$ over the (finite, nonempty) arc type; $b - 2$ is natural-number subtraction, exact since $b \ge 7$.
--
--   Differences from the source:
--   - encoding: b = ⌈6/α⌉ and η = α n̂_k as fixed values → variables b, η with hypotheses b = ⌈6/α⌉₊ and η = α·n̂_k; reason: names for the paper's values, same instances
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.13 (bound on D_S,dem and the displays following it)

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
import Definitions.Def_IPMJumpLB_Dmax
import Definitions.Def_IPMJumpLB_shortcutOutFlow
import Definitions.Def_IPMJumpLB_shortcutDemGap
import Definitions.Def_IPMJumpLB_pathGap
import Definitions.Def_IPMJumpLB_leafGap

namespace IPMJumpLB

/-- Bounds on the gap terms (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.13): at every η-iterate of the
Section 4 instance, `0 < D_S,dem < 3(b − 2)k³`,
`D_P + D_L ≤ (2k² + k) D_max ≤ (N_k/η) D ≤ D/2`, and consequently
`D/2 < 3k F_S,out + 3(b − 2)k³` and `k F_S,out < D`. -/
theorem gap_term_bounds (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ))
    (x : VertexU b k → ℝ) (f : ArcU b k → ℝ) (hit : IsEtaIterate (unitSSSP b k) η x f) :
    0 < shortcutDemGap b k x f ∧
      shortcutDemGap b k x f < 3 * ((b - 2 : ℕ) : ℝ) * (k : ℝ) ^ 3 ∧
      pathGap b k x f + leafGap b k x f ≤ (2 * (k : ℝ) ^ 2 + k) * Dmax (unitSSSP b k) x f ∧
      (2 * (k : ℝ) ^ 2 + k) * Dmax (unitSSSP b k) x f ≤
        (2 * (k : ℝ) ^ 2 + k) / η * gap (unitSSSP b k) x f ∧
      (2 * (k : ℝ) ^ 2 + k) / η * gap (unitSSSP b k) x f ≤ 1 / 2 * gap (unitSSSP b k) x f ∧
      1 / 2 * gap (unitSSSP b k) x f <
        3 * (k : ℝ) * shortcutOutFlow b k f + 3 * ((b - 2 : ℕ) : ℝ) * (k : ℝ) ^ 3 ∧
      (k : ℝ) * shortcutOutFlow b k f < gap (unitSSSP b k) x f := by sorry

end IPMJumpLB
