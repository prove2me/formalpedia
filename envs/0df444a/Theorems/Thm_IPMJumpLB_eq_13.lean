-- Prove2me | Theorems.Thm_IPMJumpLB_eq_13
-- name    : IPMJumpLB.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:53.025986+00:00
-- url     : https://prove2.me/theorems/8188948d-66a0-41a3-a66d-09bb73802e44
-- title:
--   Eq. (13) — $D_{\max} < \gamma F_{S,\mathrm{in}}$ with $\gamma = 3k/(\eta - N_k) \le 6k/\eta \le 1/2$
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$, $\eta = \alpha \hat n_k$ and $N_k = 2k^2 + k$. At every $\eta$-iterate $(x, s, f)$ of the unit-demand instance of Section 4,
--   $$
--   D_{\max} < \gamma F_{S,\mathrm{in}}, \qquad \gamma := \frac{3k}{\eta - N_k} \le \frac{6k}{\eta} \le \frac12 . \tag{13}
--   $$
--   Moreover $\eta - N_k \ge \eta/2$ and $6k/\eta \le 1/k \le 1/2$.
--
--   Equation (13) replaces (10) of the proof of Theorem 3.1 and controls every arc product $s_e f_e$ by the first-shortcut flow.
--
--   Differences from the source:
--   - encoding: b = ⌈6/α⌉ and η = α n̂_k as fixed values → variables b, η with hypotheses b = ⌈6/α⌉₊ and η = α·n̂_k; γ written out as 3k/(η − (2k² + k)); reason: names for the paper's values, same instances
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, Eq. (13) and the sentence after it, p.13

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
import Definitions.Def_IPMJumpLB_shortcutInFlow

namespace IPMJumpLB

/-- Eq. (13) (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.13): at every η-iterate of the Section 4 instance,
`D_max < γ F_S,in` with `γ := 3k/(η − N_k) ≤ 6k/η ≤ 1/2`, where `N_k = 2k² + k`; indeed
`η − N_k ≥ η/2` and `6k/η ≤ 1/k ≤ 1/2`. -/
theorem eq_13 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ))
    (x : VertexU b k → ℝ) (f : ArcU b k → ℝ) (hit : IsEtaIterate (unitSSSP b k) η x f) :
    Dmax (unitSSSP b k) x f < 3 * (k : ℝ) / (η - (2 * (k : ℝ) ^ 2 + k)) * shortcutInFlow b k f ∧
      3 * (k : ℝ) / (η - (2 * (k : ℝ) ^ 2 + k)) ≤ 6 * (k : ℝ) / η ∧
      6 * (k : ℝ) / η ≤ 1 / 2 ∧
      η / 2 ≤ η - (2 * (k : ℝ) ^ 2 + k) ∧ 6 * (k : ℝ) / η ≤ 1 / (k : ℝ) ∧
      1 / (k : ℝ) ≤ 1 / 2 := by sorry

end IPMJumpLB
