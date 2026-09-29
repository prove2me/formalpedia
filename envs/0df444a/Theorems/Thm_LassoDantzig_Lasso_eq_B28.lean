-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_eq_B28
-- name    : LassoDantzig.Lasso.eq_B28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:21:03.401766+00:00
-- url     : https://prove2.me/theorems/0f5b870b-0895-4f73-bccf-da46d4451d40
-- title:
--   Appendix B, (B.28) — $\ell_2$ norm of a cone vector versus its $m$ largest coordinates (used with $c_0=3$)
-- statement:
--   Let $s,m\in\mathbb N$ with $m\ge1$, $c_0>0$, $J_0\subseteq\{1,\dots,M\}$ with $|J_0|\le s$, and let $\delta\in\mathbb R^M$ satisfy $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$. Let $J_1$ be a set of $m$ indices outside $J_0$ carrying $m$ largest in absolute value coordinates of $\delta$ outside $J_0$, and $J_{01}=J_0\cup J_1$. Then
--   $$
--   |\delta|_2\le\Big(1+c_0\sqrt{\frac sm}\Big)|\delta_{J_{01}}|_2 .
--   $$
--
--   Under RE$(s,m,3)$ this converts the bound on $|\delta_{J_{01}}|_2$ into a bound on the full $\ell_2$ error, which feeds the $\ell_p$ bound (7.10).
--
--   **Formalization Note** The paper writes (B.28) in the proof of Theorem 7.1 with $c_0=1$; the proof of Theorem 7.2 uses it with $c_0=3$. It is stated here for every $c_0>0$. If fewer than $m$ indices lie outside $J_0$ no such $J_1$ exists; in the application $|J_0|\le s$ and $s+m\le M$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 27, Appendix B, Eq. (B.28) and the two displays preceding it (used with c0 = 3 in the proof of Theorem 7.2, p. 28)

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- (B.28), p. 27 (used with `c₀ = 3` in the proof of Theorem 7.2): if `|J₀| ≤ s`, `δ`
satisfies the cone condition `|δ_{J₀ᶜ}|_1 ≤ c₀|δ_{J₀}|_1`, `m ≥ 1`, and `J₁` is a set of
`m` largest in absolute value coordinates of `δ` outside `J₀`, then
`|δ|_2 ≤ (1 + c₀√(s/m)) |δ_{J₀₁}|_2` with `J₀₁ = J₀ ∪ J₁`. -/
theorem eq_B28 {M : ℕ} (s m : ℕ) (hm : 1 ≤ m) (c0 : ℝ) (hc0 : 0 < c0)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond c0 J0 δ)
    (J1 : Finset (Fin M)) (hJ1 : IsTopOutside m J0 δ J1) :
    euclNorm δ ≤ (1 + c0 * Real.sqrt ((s : ℝ) / m)) * l2On δ (J0 ∪ J1) := by sorry

end LassoDantzig.Lasso
