-- Prove2me | Theorems.Thm_IPMJumpLB_middle_gadget_estimates
-- name    : IPMJumpLB.middle_gadget_estimates
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:30.151353+00:00
-- url     : https://prove2.me/theorems/febb4150-0244-4269-b635-345f922befb5
-- title:
--   Proof of Theorem 4.1 — the middle gadget of a flipped block violates both (2) and (3)
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$, $\eta = \alpha \hat n_k$, $h = \lceil 12bk^2/\eta\rceil$ and $\gamma = 3k/(\eta - N_k)$ with $N_k = 2k^2 + k$. Let $(x, s, f)$ and $(x', s', f')$ be $\eta$-iterates of the unit-demand instance of Section 4 and let $0 \le i < k$ satisfy
--   $$
--   F_{S,\mathrm{out}}(f) - (2k^2 - ki) \ge kh, \qquad 2k^2 - ki - F_{S,\mathrm{out}}(f') > kh .
--   $$
--   Then
--
--   1. $f_{e_i^-} \ge kh$ and $f'_{e_i^+} > kh$;
--   2. $\displaystyle s_{e_i^-} < \gamma + \frac{bk^2\gamma}{kh} \le 1$ and $\displaystyle s'_{e_i^+} < \frac{bk^2\gamma}{kh} \le \frac{6bk^2}{\eta h} \le \frac12$;
--   3. $s_{e_i^+} > 1$ and $s'_{e_i^-} > 3/2$;
--   4. $F_{S,\mathrm{in}}(f') < bk^2$;
--   5. $\displaystyle f'_{e_i^-} < \tfrac23 D'_{\max} < \tfrac23 \gamma bk^2 \le \frac{kh}{3}$;
--   6. the move from $(x, s, f)$ to $(x', s', f')$ is not a jump: the slack of $e_i^+$ falls below half its value, violating (2), and the flow of $e_i^-$ falls below a third of its value, violating (3).
--
--   This is the core of the proof of Theorem 4.1: a jump cannot flip $2h + 1$ consecutive gadgets.
--
--   Differences from the source:
--   - generalization: the paper states the estimates for consecutive iterates ℓ, ℓ+1 of a path-following sequence whose rank drops by more than 2h, with i the middle index of 2h + 1 consecutive flipped gadgets → any two η-iterates and any 0 ≤ i < k satisfying the two displayed inequalities; reason: the two inequalities are the only facts about ℓ, ℓ+1 and i that the estimates use, and the paper derives them from the block before stating the estimates
--   - encoding: b = ⌈6/α⌉, η = α n̂_k, h = ⌈12bk²/η⌉ and γ = 3k/(η − N_k) as fixed values → variables with defining hypotheses; the paper's final contradiction stated as ¬IsJump; reason: same instances
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.14 ("As before, applying the criterion …" to "Thus (3) fails as well, a contradiction.")

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
import Definitions.Def_IPMJumpLB_IsJump
import Definitions.Def_IPMJumpLB_shortcutInFlow
import Definitions.Def_IPMJumpLB_shortcutOutFlow

namespace IPMJumpLB

/-- The middle-gadget estimates (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.14). Let `p = (x, f)` and
`q = (x', f')` be η-iterates of the Section 4 instance, `h = ⌈12bk²/η⌉`,
`γ = 3k/(η − N_k)`, and let `0 ≤ i < k` satisfy
`F_S,out(f) − (2k² − ki) ≥ kh` and `2k² − ki − F_S,out(f') > kh`. Then
`f_(e⁻ᵢ) ≥ kh`, `f'_(e⁺ᵢ) > kh`; `s_(e⁻ᵢ) < γ + bk²γ/(kh) ≤ 1`,
`s'_(e⁺ᵢ) < bk²γ/(kh) ≤ 6bk²/(ηh) ≤ 1/2`; `s_(e⁺ᵢ) > 1`; `s'_(e⁻ᵢ) > 3/2`;
`F_S,in(f') < bk²`; `f'_(e⁻ᵢ) < (2/3) D'_max < (2/3) γ bk² ≤ kh/3`; and the move from `p` to `q`
is not a jump. -/
theorem middle_gadget_estimates (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) (hk : 3 ≤ k)
    (b : ℕ) (hb : b = ⌈6 / α⌉₊) (η : ℝ) (hη : η = α * (nHat b k : ℝ))
    (h : ℕ) (hh : h = ⌈12 * (b : ℝ) * (k : ℝ) ^ 2 / η⌉₊)
    (γ : ℝ) (hγ : γ = 3 * (k : ℝ) / (η - (2 * (k : ℝ) ^ 2 + k)))
    (p q : (VertexU b k → ℝ) × (ArcU b k → ℝ))
    (hp : IsEtaIterate (unitSSSP b k) η p.1 p.2) (hq : IsEtaIterate (unitSSSP b k) η q.1 q.2)
    (i : Fin k)
    (h1 : (k : ℝ) * h ≤ shortcutOutFlow b k p.2 - (2 * (k : ℝ) ^ 2 - (k : ℝ) * (i : ℕ)))
    (h2 : (k : ℝ) * h < 2 * (k : ℝ) ^ 2 - (k : ℝ) * (i : ℕ) - shortcutOutFlow b k q.2) :
    (k : ℝ) * h ≤ p.2 (.bwd i) ∧ (k : ℝ) * h < q.2 (.fwd i) ∧
      slack (unitSSSP b k) p.1 (.bwd i) < γ + (b : ℝ) * (k : ℝ) ^ 2 * γ / ((k : ℝ) * h) ∧
      γ + (b : ℝ) * (k : ℝ) ^ 2 * γ / ((k : ℝ) * h) ≤ 1 ∧
      slack (unitSSSP b k) q.1 (.fwd i) < (b : ℝ) * (k : ℝ) ^ 2 * γ / ((k : ℝ) * h) ∧
      (b : ℝ) * (k : ℝ) ^ 2 * γ / ((k : ℝ) * h) ≤ 6 * (b : ℝ) * (k : ℝ) ^ 2 / (η * h) ∧
      6 * (b : ℝ) * (k : ℝ) ^ 2 / (η * h) ≤ 1 / 2 ∧
      1 < slack (unitSSSP b k) p.1 (.fwd i) ∧
      3 / 2 < slack (unitSSSP b k) q.1 (.bwd i) ∧
      shortcutInFlow b k q.2 < (b : ℝ) * (k : ℝ) ^ 2 ∧
      q.2 (.bwd i) < 2 / 3 * Dmax (unitSSSP b k) q.1 q.2 ∧
      2 / 3 * Dmax (unitSSSP b k) q.1 q.2 < 2 / 3 * γ * ((b : ℝ) * (k : ℝ) ^ 2) ∧
      2 / 3 * γ * ((b : ℝ) * (k : ℝ) ^ 2) ≤ (k : ℝ) * h / 3 ∧
      ¬ IsJump (unitSSSP b k) η p q := by sorry

end IPMJumpLB
