-- Prove2me | Theorems.Thm_MinimaxSLP_RhsExtremal_mixture_lower_bound
-- name    : MinimaxSLP.RhsExtremal.mixture_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:08.379667+00:00
-- url     : https://prove2.me/theorems/f40f7449-f5a8-4226-ab98-03d43c1b1c97
-- title:
--   Proof of Theorem 3.3, p. 591 — E_{P_m(x)}[𝕌(𝒬(h̃, x))] is at least the objective of (16)
-- statement:
--   Under Assumptions 2, 3 (at the constant $q$) and 5, and $\alpha_k\ge 0$, let $(V_k^i,v_k^i,v_{k0}^i)_{k,i}$ be a feasible point of (16) in which every block has $v_{k0}^i>0$ or is zero, and let $P_m(x)$ be the associated mixture of normal distributions. Then $h\mapsto\mathbb U(\mathcal Q(h,x))$ is $P_m(x)$-integrable and
--   $$
--   \mathbb E_{P_m(x)}\big[\mathbb U(\mathcal Q(\tilde h,x))\big]\ \ge\ \sum_{k=1}^K\sum_{i=1}^N\big(\alpha_k p_i'v_k^i+v_{k0}^i(\beta_k-\alpha_k p_i'Tx)\big).
--   $$
--
--   Applied to an optimal solution of (16), the right-hand side is $\hat Z_{DD}(x)$; this is the lower half of the sandwich that proves Theorem 3.3.
--
--   **Formalization Note** The statement is made for every feasible point with zero-or-positive blocks, not only for an optimal one; the paper's last display, with "$=\hat Z_{DD}(x)$", is the specialization to an optimal point.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 591, proof of Theorem 3.3

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model

namespace MinimaxSLP.RhsExtremal

open MeasureTheory Matrix

/-- Proof of Theorem 3.3, p. 591: for every feasible `s` of (16) whose blocks have
`v_k0^i > 0` or are zero, `𝕌(𝒬(·, x))` is integrable under the mixture `P_m(x)` and
`E_{P_m(x)}[𝕌(𝒬(h̃, x))] ≥ Σ_{k,i} (α_k p_i′v_k^i + v_k0^i (β_k − α_k p_i′T x))`, the objective
of (16) at `s`. -/
theorem mixture_lower_bound {r d n K N : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ)
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ))
    (hs : s ∈ feasible16 K N μ Q)
    (hpos : ∀ k i, 0 < (s k i).2.2 ∨ s k i = 0) :
    Integrable (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) (mixture s) ∧
    obj16 T α β ps x s ≤ ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂(mixture s) := by sorry

end MinimaxSLP.RhsExtremal
