-- Prove2me | Theorems.Thm_LassoDantzig_Equivalence_eq_B17_lasso_side
-- name    : LassoDantzig.Equivalence.eq_B17_lasso_side
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:06:01.710099+00:00
-- url     : https://prove2.me/theorems/aa0234f5-588d-4a00-b4c7-16a85af7ac5b
-- title:
--   Appendix B, Eq. (B.17) — $\|\hat f_L-f\|_n^2\le\|\hat f_D-f\|_n^2+9f_{\max}^2r^2\mathcal M(\hat\beta_L)/\kappa^2$ on $\mathcal A$
-- statement:
--   Let $n\ge1$, $M\ge2$, $1\le s\le M$, $X\in\mathbb R^{n\times M}$ with $\|f_j\|_n\ne0$ for all $j$, $f,w\in\mathbb R^n$, $r>0$, and $y=f+w$. Assume RE$(s,1)$ holds with witness $\kappa>0$. Suppose the noise lies in the event $\mathcal A=\bigcap_j\{2|\tfrac1n\sum_iX_{ij}w_i|\le r\|f_j\|_n\}$. Then for every Lasso solution $\hat\beta_L$ with $\mathcal M(\hat\beta_L)\le s$ and every Dantzig selector $\hat\beta_D$ (both for the data $y$ and the same $r$),
--   $$
--   \|\hat f_L-f\|_n^2\le\|\hat f_D-f\|_n^2+\frac{9f_{\max}^2r^2\mathcal M(\hat\beta_L)}{\kappa^2}.
--   $$
--
--   This is the other side of the two-sided bound (5.1) of Theorem 5.1.
--
--   **Formalization Note** The paper states (B.17) "with probability at least $1-M^{1-A^2/8}$"; the statement here is the deterministic inequality on the event $\mathcal A$ from which that follows. $\kappa$ is any witness of RE$(s,1)$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 24, Appendix B, proof of Theorem 5.1, Eqs. (B.16)–(B.17)

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- (B.17), deterministic form: on the event `𝒜`, under RE(s, 1) with witness `κ`, for every
Lasso solution `β̂_L` with `𝓜(β̂_L) ≤ s` and every Dantzig selector `β̂_D`,
`‖f̂_L − f‖_n² ≤ ‖f̂_D − f‖_n² + 9 f_max² r² 𝓜(β̂_L) / κ²`. -/
theorem eq_B17_lasso_side {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (r : ℝ) (hr : 0 < r) (hw : NoiseEventHalf X r w)
    (βL βD : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βL)
    (hD : IsDantzig X (fun i => f i + w i) r βD) (hsp : sparsity βL ≤ s) :
    predLoss X f βL ≤
      predLoss X f βD + 9 * fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2 := by sorry

end LassoDantzig.Equivalence
