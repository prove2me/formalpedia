-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_eq_B30_B31
-- name    : LassoDantzig.Lasso.eq_B30_B31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:20:12.489985+00:00
-- url     : https://prove2.me/theorems/a88d78bb-4aa5-4997-9e86-ee1bab0f993d
-- title:
--   Appendix B, (B.30)–(B.31) — prediction and $\ell_2$ bounds for the Lasso on the event $\mathcal A$
-- statement:
--   Let $n\ge1$, $M\ge2$, $1\le s\le M$, let $X\in\mathbb R^{n\times M}$ have unit diagonal Gram matrix, and let $\beta^*\in\mathbb R^M$ satisfy $\mathcal M(\beta^*)\le s$. Assume RE$(s,3)$ holds with witness $\kappa>0$. Let $r>0$ and let $w\in\mathbb R^n$ lie in the noise event $\mathcal A$, i.e. $2\big|\frac1n\sum_iX_{ij}w_i\big|\le r$ for all $j$. Let $\hat\beta_L$ be any Lasso solution (7.2) for $y=X\beta^*+w$, and put $\delta=\hat\beta_L-\beta^*$, $J_0=J(\beta^*)$. Then
--   $$
--   \frac1n|X\delta|_2^2\le4r\sqrt s\,|\delta_{J_0}|_2,\qquad\text{(B.30)}
--   $$
--   the cone condition $|\delta_{J_0^c}|_1\le3|\delta_{J_0}|_1$ holds, and
--   $$
--   \frac1n|X\delta|_2^2\le\frac{16r^2s}{\kappa^2},\qquad|\delta_{J_0}|_2\le\frac{4r\sqrt s}{\kappa^2}.\qquad\text{(B.31)}
--   $$
--
--   The first inequality of (B.31) is the prediction bound (7.8); the second, combined with the cone condition, gives the $\ell_1$ bound (7.7).
--
--   **Formalization Note** The paper states these inequalities "on the event $\mathcal A$" with $r=A\sigma\sqrt{\log M/n}$; they are deterministic consequences of the event, so they are stated for every noise vector $w$ in $\mathcal A$ and every $r>0$. $\kappa$ is any witness of RE$(s,3)$, in place of $\kappa(s,3)$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 28, Appendix B, Eqs. (B.30), (B.31) (proof of Theorem 7.2)

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- (B.30)–(B.31), p. 28 (proof of Theorem 7.2): for `r > 0`, on the noise event `𝒜`, for `y = Xβ* + w`
with unit diagonal, `𝓜(β*) ≤ s` and Assumption RE(s, 3) with witness `κ`, every Lasso solution
`β̂` satisfies, with `δ = β̂ − β*` and `J₀ = J(β*)`,
`(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀}|_2` (B.30), the cone condition (4.1) with `c₀ = 3`, and
`(1/n)|Xδ|_2² ≤ 16 r² s / κ²`, `|δ_{J₀}|_2 ≤ 4r√s / κ²` (B.31). -/
theorem eq_B30_B31 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X) (βstar : Fin M → ℝ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (hsparse : sparsity βstar ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 3 κ)
    (r : ℝ) (hr : 0 < r) (w : Fin n → ℝ) (hw : NoiseEventHalf X r w)
    (βhat : Fin M → ℝ) (hL : IsLasso X (fun i => X.mulVec βstar i + w i) r βhat) :
    (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 ≤
        4 * r * Real.sqrt s * l2On (βhat - βstar) (supp βstar) ∧
      ConeCond 3 (supp βstar) (βhat - βstar) ∧
      (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 ≤ 16 * r ^ 2 * s / κ ^ 2 ∧
      l2On (βhat - βstar) (supp βstar) ≤ 4 * r * Real.sqrt s / κ ^ 2 := by sorry

end LassoDantzig.Lasso
