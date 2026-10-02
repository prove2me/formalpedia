-- Prove2me | Theorems.Thm_LassoDantzig_Equivalence_theorem_5_1
-- name    : LassoDantzig.Equivalence.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:06:45.171784+00:00
-- url     : https://prove2.me/theorems/df790842-7a44-4862-9b98-3e3583bb0d04
-- title:
--   Theorem 5.1 — approximate equivalence of the Lasso and Dantzig prediction losses
-- statement:
--   Let $n\ge1$ and $M\ge2$. Let $X=(f_j(Z_i))\in\mathbb R^{n\times M}$ be the design matrix of a dictionary $f_1,\dots,f_M$ at design points $Z_1,\dots,Z_n$, with empirical column norms $\|f_j\|_n=(\tfrac1n\sum_iX_{ij}^2)^{1/2}\ne0$, and let $f=(f(Z_1),\dots,f(Z_n))\in\mathbb R^n$ be arbitrary (the regression function is not assumed to be a combination of the $f_j$). Let $W_1,\dots,W_n$ be independent $\mathcal N(0,\sigma^2)$ random variables with $\sigma>0$, and observe $y=f+W$. Let Assumption RE$(s,1)$ hold with $1\le s\le M$ and witness $\kappa>0$. Let $A>2\sqrt2$ and
--   $$
--   r=A\sigma\sqrt{\frac{\log M}{n}} .
--   $$
--   Then there is an event of probability at least $1-M^{1-A^2/8}$ on which, for every Lasso solution $\hat\beta_L$ of (2.1) and every Dantzig selector $\hat\beta_D$ of (2.4) (both with this $r$) such that $\mathcal M(\hat\beta_L)\le s$,
--   $$
--   \Big|\,\|\hat f_D-f\|_n^2-\|\hat f_L-f\|_n^2\,\Big|\le16A^2\,\frac{\mathcal M(\hat\beta_L)\sigma^2}{n}\,\frac{f_{\max}^2}{\kappa^2}\,\log M ,
--   $$
--   where $\hat f_L=X\hat\beta_L$, $\hat f_D=X\hat\beta_D$, $\|g-f\|_n^2=\tfrac1n\sum_i(g_i-f_i)^2$ and $f_{\max}=\max_j\|f_j\|_n$.
--
--   The two estimators thus have prediction losses that differ by at most the rate $\mathcal M(\hat\beta_L)\sigma^2\log M/n$ of a sparse regression with $\mathcal M(\hat\beta_L)$ parameters, up to the factor $f_{\max}^2/\kappa^2$ measuring how ill-posed the Gram matrix is on sparse vectors. Any prediction bound proved for one estimator then transfers to the other at this cost.
--
--   **Formalization Note** $\kappa$ is any witness of RE$(s,1)$; the paper's $\kappa(s,1)$ is the largest witness and the bound decreases in $\kappa$, so the two formulations are equivalent. The condition "$\mathcal M(\hat\beta_L)\le s$" concerns the realised Lasso solution and is required inside the event, for each $\omega$ and each solution; the event itself does not depend on the solutions. Neither estimator need be unique and the bound holds for all of them. The law of $W_i$ is Mathlib's `gaussianReal 0 σ²`, with each $W_i$ measurable and the family mutually independent; $\log$ is the natural logarithm; the event is measurable and its probability is taken as a real number.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, pp. 11–12, Theorem 5.1, Eq. (5.1)

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Equivalence

/-- Theorem 5.1 (Bickel–Ritov–Tsybakov): approximate equivalence of the Lasso and Dantzig
prediction losses. With probability at least `1 − M^{1 − A²/8}`, for every Lasso solution
`β̂_L` with `𝓜(β̂_L) ≤ s` and every Dantzig selector `β̂_D` (same `r = Aσ√(log M / n)`),
`|‖f̂_D − f‖_n² − ‖f̂_L − f‖_n²| ≤ 16 A² (𝓜(β̂_L) σ² / n) (f_max² / κ²) log M`. -/
theorem theorem_5_1 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f : Fin n → ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βL βD : Fin M → ℝ,
        IsLasso X (fun i => f i + W i ω) r βL → IsDantzig X (fun i => f i + W i ω) r βD →
        sparsity βL ≤ s →
        |predLoss X f βD - predLoss X f βL| ≤
          16 * A ^ 2 * ((sparsity βL : ℝ) * σ ^ 2 / n) * (fmax X ^ 2 / κ ^ 2) * Real.log M := by sorry

end LassoDantzig.Equivalence
