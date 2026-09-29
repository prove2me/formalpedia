-- Prove2me | Theorems.Thm_LassoDantzig_Equivalence_eq_B15_dantzig_side
-- name    : LassoDantzig.Equivalence.eq_B15_dantzig_side
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:04:41.587484+00:00
-- url     : https://prove2.me/theorems/8bb91e4e-0d99-4cb6-8508-42e3de37fbb8
-- title:
--   Appendix B, Eq. (B.15) — $\|\hat f_D-f\|_n^2\le\|\hat f_L-f\|_n^2+16f_{\max}^2r^2\mathcal M(\hat\beta_L)/\kappa^2$ on $\mathcal B$
-- statement:
--   Let $n\ge1$, $M\ge2$, $1\le s\le M$, $X\in\mathbb R^{n\times M}$ with $\|f_j\|_n\ne0$ for all $j$, $f,w\in\mathbb R^n$, $r>0$, and $y=f+w$. Assume RE$(s,1)$ holds with witness $\kappa>0$: $\kappa\sqrt n|\delta_{J_0}|_2\le|X\delta|_2$ whenever $|J_0|\le s$, $\delta\ne0$ and $|\delta_{J_0^c}|_1\le|\delta_{J_0}|_1$. Suppose the noise lies in the event $\mathcal B=\bigcap_j\{|\tfrac1n\sum_iX_{ij}w_i|\le r\|f_j\|_n\}$. Then for every Lasso solution $\hat\beta_L$ with $\mathcal M(\hat\beta_L)\le s$ and every Dantzig selector $\hat\beta_D$ (both for the data $y$ and the same $r$),
--   $$
--   \|\hat f_D-f\|_n^2\le\|\hat f_L-f\|_n^2+\frac{16f_{\max}^2r^2\mathcal M(\hat\beta_L)}{\kappa^2},
--   $$
--   where $\hat f_L=X\hat\beta_L$, $\hat f_D=X\hat\beta_D$ and $\|g-f\|_n^2=\tfrac1n\sum_i(g_i-f_i)^2$.
--
--   This is one side of the two-sided bound (5.1) of Theorem 5.1.
--
--   **Formalization Note** The paper states (B.15) "with probability at least $1-M^{1-A^2/2}$"; the statement here is the deterministic inequality on the event $\mathcal B$ from which that follows. $\kappa$ is any witness of RE$(s,1)$ (see the definition file); the paper's $\kappa(s,1)$ is the largest one.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 24, Appendix B, proof of Theorem 5.1, Eq. (B.15)

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- (B.15), deterministic form: on the event `ℬ`, under RE(s, 1) with witness `κ`, for every
Lasso solution `β̂_L` with `𝓜(β̂_L) ≤ s` and every Dantzig selector `β̂_D`,
`‖f̂_D − f‖_n² ≤ ‖f̂_L − f‖_n² + 16 f_max² r² 𝓜(β̂_L) / κ²`. -/
theorem eq_B15_dantzig_side {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (r : ℝ) (hr : 0 < r) (hw : NoiseEvent X r w)
    (βL βD : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βL)
    (hD : IsDantzig X (fun i => f i + w i) r βD) (hsp : sparsity βL ≤ s) :
    predLoss X f βD ≤
      predLoss X f βL + 16 * fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2 := by sorry

end LassoDantzig.Equivalence
