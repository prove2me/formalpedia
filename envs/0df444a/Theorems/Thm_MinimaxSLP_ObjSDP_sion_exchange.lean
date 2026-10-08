-- Prove2me | Theorems.Thm_MinimaxSLP_ObjSDP_sion_exchange
-- name    : MinimaxSLP.ObjSDP.sion_exchange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:07.738823+00:00
-- url     : https://prove2.me/theorems/39eda5b1-51ad-4960-994d-f9672e18ea98
-- title:
--   Proof of Theorem 2.1, p. 583 — the Sion exchange $\inf_q\max_{w\in X(x)} = \max_{w\in X(x)}\inf_q$
-- statement:
--   Let $X(x)$ be a nonempty bounded recourse set, let $Y\succeq 0$, $y\in\mathbb R^d$ and $y_0,a,b\in\mathbb R$ (in the paper $a=\alpha_k$, $b=\beta_k$), and put
--   $$
--   g(q,w)=q'Yq+q'y+y_0-a\,q'w-b .
--   $$
--   Then, with values in the extended reals,
--   $$
--   \inf_{q\in\mathbb R^d}\ \max_{w\in X(x)} g(q,w)\;=\;\max_{w\in X(x)}\ \inf_{q\in\mathbb R^d} g(q,w),
--   $$
--   and the maximum on the right is attained at some $w_0\in X(x)$.
--
--   This is the application of Sion's minimax theorem in the proof of Theorem 2.1: $g$ is convex in $q$ because $Y\succeq 0$ and affine in $w$, and $X(x)$ is compact and convex.
--
--   **Formalization Note** The values are taken in `EReal`, because $\inf_q g(q,w)=-\infty$ when $y-a w$ is not in the range of $Y$. The supremum over $w\in X(x)$ is written as an `EReal` supremum, and its attainment on the right is stated explicitly.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 583, proof of Theorem 2.1 (Sion minimax step, citing Sion [25])

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP

/-- Proof of Theorem 2.1 (p. 583), the Sion step: for `Y ⪰ 0`, `a = α_k ≥ 0` (any real `a`
works) and a nonempty bounded recourse set `X(x)`, with
`g(q, w) = q′Yq + q′y + y₀ − a q′w − b`,
`inf_{q ∈ ℝ^d} max_{w ∈ X(x)} g(q, w) = max_{w ∈ X(x)} inf_{q ∈ ℝ^d} g(q, w)`,
and the outer maximum on the right is attained. Values are taken in `EReal`, because
`inf_q g(q, w)` is `−∞` for some `w`. -/
theorem sion_exchange {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (hbdd : Bornology.IsBounded (recourseSet W T h x))
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.PosSemidef) (y : Fin d → ℝ) (y₀ a b : ℝ) :
    (⨅ q : Fin d → ℝ, ⨆ w ∈ recourseSet W T h x,
        ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b : ℝ) : EReal)) =
      (⨆ w ∈ recourseSet W T h x, ⨅ q : Fin d → ℝ,
        ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b : ℝ) : EReal)) ∧
    ∃ w₀ ∈ recourseSet W T h x,
      (⨅ q : Fin d → ℝ, ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w₀) - b : ℝ) : EReal)) =
        ⨆ w ∈ recourseSet W T h x, ⨅ q : Fin d → ℝ,
          ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b : ℝ) : EReal) := by sorry

end MinimaxSLP.ObjSDP
