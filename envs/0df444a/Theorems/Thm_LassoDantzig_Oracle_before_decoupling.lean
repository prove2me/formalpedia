-- Prove2me | Theorems.Thm_LassoDantzig_Oracle_before_decoupling
-- name    : LassoDantzig.Oracle.before_decoupling
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:10:16.156808+00:00
-- url     : https://prove2.me/theorems/8e530a9c-6f53-45e1-abd7-5359bc88d149
-- title:
--   Proof of Theorem 6.1 — the inequality before decoupling
-- statement:
--   Let $n\ge1$, $M\ge2$, $1\le s\le M$, $X\in\mathbb R^{n\times M}$ with nonzero column norms, $f,y\in\mathbb R^n$, $r>0$ and $\varepsilon>0$. Assume RE$(s,(3+4/\varepsilon)f_{\max}/f_{\min})$ holds with witness $\kappa>0$, and that $w=y-f$ lies in the noise event $\mathcal A$. Let $\hat\beta$ be any Lasso solution (2.1) for $y$ with tuning constant $r$, $\hat f=X\hat\beta$, and let $\beta\in\mathbb R^M$ with $\mathcal M(\beta)\le s$ be in case (B.24), $\varepsilon\|X\beta-f\|_n^2<4r\sum_{j\in J(\beta)}\|f_j\|_n|\hat\beta_j-\beta_j|$. Then
--   $$\begin{aligned}\|\hat f-f\|_n^2&\le\|X\beta-f\|_n^2+4rf_{\max}\kappa^{-1}\sqrt{\mathcal M(\beta)}\,\|\hat f-X\beta\|_n\\&\le\|X\beta-f\|_n^2+4rf_{\max}\kappa^{-1}\sqrt{\mathcal M(\beta)}\,\big(\|\hat f-f\|_n+\|X\beta-f\|_n\big).\end{aligned}$$
--
--   This is the point where the restricted eigenvalue assumption enters the oracle inequality.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 26, Appendix B, proof of Theorem 6.1, display after "using that |δ_{J0}|_2 ≤ fmax|δ′_{J0}|_2 we find"

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Inequality before decoupling in the proof of Theorem 6.1** (p. 26, display after "using
that `|δ_{J₀}|_2 ≤ f_max|δ'_{J₀}|_2` we find"). Assume RE(s, (3 + 4/ε) f_max/f_min) with witness
`κ > 0`. On the event `𝒜`, for every Lasso solution `β̂` with tuning constant `r > 0` and every
`β` with `𝓜(β) ≤ s` in case (B.24):
`‖f̂_L − f‖_n² ≤ ‖f_β − f‖_n² + 4r f_max κ⁻¹ √𝓜(β) ‖f̂_L − f_β‖_n
  ≤ ‖f_β − f‖_n² + 4r f_max κ⁻¹ √𝓜(β) (‖f̂_L − f‖_n + ‖f_β − f‖_n)`. -/
theorem before_decoupling {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hA : NoiseBound X (fun i => y i - f i) r) (ε : ℝ) (hε : 0 < ε)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ)
    (hRE : RE X s ((3 + 4 / ε) * fmax X / fmin X) κ)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ) (hβs : sparsity β ≤ s)
    (hB24 : ε * empSq (fun i => X.mulVec β i - f i) <
      4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j|) :
    empSq (fun i => X.mulVec βhat i - f i) ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * fmax X * κ⁻¹ * Real.sqrt (sparsity β) *
            empNorm (fun i => X.mulVec βhat i - X.mulVec β i) ∧
      empSq (fun i => X.mulVec β i - f i) +
          4 * r * fmax X * κ⁻¹ * Real.sqrt (sparsity β) *
            empNorm (fun i => X.mulVec βhat i - X.mulVec β i) ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * fmax X * κ⁻¹ * Real.sqrt (sparsity β) *
            (empNorm (fun i => X.mulVec βhat i - f i) + empNorm (fun i => X.mulVec β i - f i)) := by sorry

end LassoDantzig.Oracle
