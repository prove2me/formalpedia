-- Prove2me | Theorems.Thm_MinimaxSLP_ObjSDP_Y_posSemidef
-- name    : MinimaxSLP.ObjSDP.Y_posSemidef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:58.28844+00:00
-- url     : https://prove2.me/theorems/6d0591f8-c6d4-4572-8593-784c3325b342
-- title:
--   Proof of Theorem 2.1, p. 583 — a dual-feasible $Y$ satisfying $(\mathcal C_k)$ is positive semidefinite
-- statement:
--   Let $W$, $T$, $h$ be as in the model with Assumption 3 ($\{\pi : W'\pi\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$), let $x$ have a nonempty recourse set $X(x)$, and fix a piece $k$ with $\alpha_k\ge 0$. Let $Y\in\mathbb R^{d\times d}$ be symmetric, $y\in\mathbb R^d$ and $y_0\in\mathbb R$, and suppose the constraint
--   $$
--   (\mathcal C_k):\qquad q'Yq+q'y+y_0\ \ge\ \alpha_k\,\mathcal Q(q,x)+\beta_k\qquad\forall q\in\mathbb R^d
--   $$
--   holds. Then $Y\succeq 0$.
--
--   In the proof of Theorem 2.1 this is the first step: it makes the function $q\mapsto q'Yq+q'y+y_0-\alpha_k q'w_k-\beta_k$ convex, which the minimax exchange needs.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 583, proof of Theorem 2.1 ("We first claim that Y ⪰ 0")

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP

/-- Proof of Theorem 2.1 (p. 583): if `(Y, y, y₀)` with `Y` symmetric satisfies the constraint
`(𝒞_k)`: `q′Yq + q′y + y₀ ≥ α_k 𝒬(q, x) + β_k` for all `q ∈ ℝ^d`, for one piece `k` with
`α_k ≥ 0`, then `Y ⪰ 0`. -/
theorem Y_posSemidef {n r d K : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (k : Fin K) (hαk : 0 ≤ α k)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.IsSymm) (y : Fin d → ℝ) (y₀ : ℝ)
    (hC : ∀ q : Fin d → ℝ, α k * Qval W T h q x + β k ≤ q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀) :
    Y.PosSemidef := by sorry

end MinimaxSLP.ObjSDP
