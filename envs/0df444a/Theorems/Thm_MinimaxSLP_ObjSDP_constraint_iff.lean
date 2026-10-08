-- Prove2me | Theorems.Thm_MinimaxSLP_ObjSDP_constraint_iff
-- name    : MinimaxSLP.ObjSDP.constraint_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:37.819778+00:00
-- url     : https://prove2.me/theorems/6d130aa7-a900-4c88-aa98-4346f6ef3360
-- title:
--   Proof of Theorem 2.1, p. 583 — $(\mathcal C_k)$ holds iff some $w_k\in X(x)$ works for every $q$
-- statement:
--   Let $W$, $T$, $h$ satisfy Assumption 3 ($\{\pi : W'\pi\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$), let $x$ have a nonempty recourse set $X(x)$, and fix a piece $k$ with $\alpha_k\ge 0$. For a symmetric $Y\in\mathbb R^{d\times d}$, $y\in\mathbb R^d$ and $y_0\in\mathbb R$, the constraint
--   $$
--   (\mathcal C_k):\qquad q'Yq+q'y+y_0\ \ge\ \alpha_k\,\mathcal Q(q,x)+\beta_k\qquad\forall q\in\mathbb R^d
--   $$
--   is equivalent to
--   $$
--   \exists\, w_k\in X(x)\quad \forall q\in\mathbb R^d:\qquad q'Yq+q'y+y_0-\alpha_k\,q'w_k-\beta_k\ \ge 0 .
--   $$
--
--   The left side quantifies "for all $q$, there is a $w$" (through the minimum defining $\mathcal Q$); the right side has one $w_k$ for all $q$. This exchange of quantifiers is what turns the semi-infinite dual (6) into the finite semidefinite program (8).
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 583, proof of Theorem 2.1 ("Thus the constraint (𝒞_k) is equivalent to the following constraint")

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP

/-- Proof of Theorem 2.1 (p. 583): for `Y` symmetric and `α_k ≥ 0`, the constraint `(𝒞_k)`
`∀ q ∈ ℝ^d, q′Yq + q′y + y₀ ≥ α_k 𝒬(q, x) + β_k` is equivalent to
`∃ w_k ∈ X(x), ∀ q ∈ ℝ^d, q′Yq + q′y + y₀ − α_k q′w_k − β_k ≥ 0`. -/
theorem constraint_iff {n r d K : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (k : Fin K) (hαk : 0 ≤ α k)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.IsSymm) (y : Fin d → ℝ) (y₀ : ℝ) :
    (∀ q : Fin d → ℝ, α k * Qval W T h q x + β k ≤ q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀) ↔
      ∃ w ∈ recourseSet W T h x, ∀ q : Fin d → ℝ,
        0 ≤ q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - α k * (q ⬝ᵥ w) - β k := by sorry

end MinimaxSLP.ObjSDP
