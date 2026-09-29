-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_eq_B27
-- name    : LassoDantzig.Lasso.eq_B27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:20:42.253473+00:00
-- url     : https://prove2.me/theorems/b9eaaf02-4a70-4b5a-bb13-766a5e0ecfd3
-- title:
--   Appendix B, (B.27) — $\ell_1$ norm of a cone vector (used with $c_0=3$)
-- statement:
--   Let $s\in\mathbb N$, $c_0>0$, $J_0\subseteq\{1,\dots,M\}$ with $|J_0|\le s$, and let $\delta\in\mathbb R^M$ satisfy the cone condition $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$. Then
--   $$
--   |\delta|_1=|\delta_{J_0}|_1+|\delta_{J_0^c}|_1\le(1+c_0)|\delta_{J_0}|_1\le(1+c_0)\sqrt s\,|\delta_{J_0}|_2 .
--   $$
--
--   In the proof of Theorem 7.2 this is used with $c_0=3$ to pass from the $\ell_2$ bound (B.31) on $\delta_{J_0}$ to the $\ell_1$ bound (7.7).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 27, Appendix B, Eq. (B.27) (used with c0 = 3 in the proof of Theorem 7.2, p. 28)

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- (B.27), p. 27: if `δ` satisfies the cone condition `|δ_{J₀ᶜ}|_1 ≤ c₀|δ_{J₀}|_1` and
`|J₀| ≤ s`, then `|δ|_1 = |δ_{J₀}|_1 + |δ_{J₀ᶜ}|_1 ≤ (1 + c₀)|δ_{J₀}|_1 ≤ (1 + c₀)√s |δ_{J₀}|_2`.
Used with `c₀ = 3` in the proof of Theorem 7.2. -/
theorem eq_B27 {M : ℕ} (s : ℕ) (c0 : ℝ) (hc0 : 0 < c0)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond c0 J0 δ) :
    l1Norm δ = l1On δ J0 + l1On δ J0ᶜ ∧
      l1On δ J0 + l1On δ J0ᶜ ≤ (1 + c0) * l1On δ J0 ∧
      (1 + c0) * l1On δ J0 ≤ (1 + c0) * Real.sqrt s * l2On δ J0 := by sorry

end LassoDantzig.Lasso
