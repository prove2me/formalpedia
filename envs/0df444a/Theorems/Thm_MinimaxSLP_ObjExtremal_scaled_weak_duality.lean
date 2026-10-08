-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_scaled_weak_duality
-- name    : MinimaxSLP.ObjExtremal.scaled_weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:56.102071+00:00
-- url     : https://prove2.me/theorems/466a1509-8eac-40b2-9fda-171d5951b328
-- title:
--   Proof of Theorem 2.2, p. 586 — if $W'p\le\alpha v$ with $\alpha\ge0$ then $\alpha\,\mathcal Q(v,x)\ge(h-Tx)'p$
-- statement:
--   Let $x$ be such that $X(x)\neq\emptyset$, and assume Assumption 3. Let $\alpha\ge 0$, $v\in\mathbb R^d$ and $p\in\mathbb R^r$ with $W'p\le\alpha v$, i.e. $p$ is a dual feasible solution of the second-stage problem $\mathcal Q(\alpha v,x)$. Then
--   $$
--   \alpha\,\mathcal Q(v,x)\ \ge\ (h-Tx)'p .
--   $$
--
--   In the proof of Theorem 2.2 this is applied to each block $(v_k,p_k)$ of an optimal solution of (9), whose constraint is $W'p_k\le\alpha_k v_k$.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 586, proof of Theorem 2.2

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- Proof of Theorem 2.2 (p. 586): if `p` is dual feasible for `𝒬(α v, x)`, i.e.
`W′p ≤ α v`, with `α ≥ 0`, then `α 𝒬(v, x) ≥ (h − T x)′p`. -/
theorem scaled_weak_duality {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (a : ℝ) (ha : 0 ≤ a) (v : Fin d → ℝ) (π : Fin r → ℝ) (hπ : Wᵀ *ᵥ π ≤ a • v) :
    (h - T *ᵥ x) ⬝ᵥ π ≤ a * MinimaxSLP.ObjSDP.Qval W T h v x := by sorry

end MinimaxSLP.ObjExtremal
