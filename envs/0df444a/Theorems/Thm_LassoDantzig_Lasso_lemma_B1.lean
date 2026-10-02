-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_lemma_B1
-- name    : LassoDantzig.Lasso.lemma_B1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:19:08.27371+00:00
-- url     : https://prove2.me/theorems/28b29a80-d24f-49c9-a04b-366a7e9f2d8b
-- title:
--   Lemma B.1 (Section 7 case) — basic inequality, residual correlation and sparsity bound for the Lasso
-- statement:
--   Let $n\ge1$, $M\ge2$, let $X\in\mathbb R^{n\times M}$ satisfy $\frac1n\sum_iX_{ij}^2=1$ for all $j$, let $\beta^*\in\mathbb R^M$, and observe $y=X\beta^*+w$ where $w=(W_1,\dots,W_n)$ has independent $\mathcal N(0,\sigma^2)$ entries, $\sigma>0$. Let $A>2\sqrt2$ and $r=A\sigma\sqrt{\log M/n}$, and write $\|f_\beta-f\|_n^2=\frac1n|X(\beta-\beta^*)|_2^2$. Let $\phi_{\max}$ be the largest eigenvalue of $X^\top X/n$.
--
--   Then there is an event of probability at least $1-M^{1-A^2/8}$ on which every Lasso solution $\hat\beta_L$ of (7.2) satisfies:
--
--   1. simultaneously for all $\beta\in\mathbb R^M$,
--   $$
--   \|f_{\hat\beta_L}-f\|_n^2+r\sum_{j=1}^M|\hat\beta_{j,L}-\beta_j|\le\|f_\beta-f\|_n^2+4r\sum_{j\in J(\beta)}|\hat\beta_{j,L}-\beta_j|\le\|f_\beta-f\|_n^2+4r\sqrt{\mathcal M(\beta)}\Big(\sum_{j\in J(\beta)}|\hat\beta_{j,L}-\beta_j|^2\Big)^{1/2};\qquad\text{(B.1)}
--   $$
--   2. $\big|\frac1nX^\top(X\beta^*-X\hat\beta_L)\big|_\infty\le 3r/2$; (B.2)
--   3. $\mathcal M(\hat\beta_L)\le4\phi_{\max}\,\|f_{\hat\beta_L}-f\|_n^2/r^2$. (B.3)
--
--   With $\beta=\beta^*$ the first inequality is the starting point of the proof of Theorem 7.2, and (B.3) turns the prediction bound into the sparsity bound (7.9).
--
--   **Formalization Note** The paper states Lemma B.1 for the nonparametric model $y=f+w$ and the weighted Lasso (2.1). This item is its specialisation to the linear model of Section 7, the form in which the proof of Theorem 7.2 uses it: unit column norms $\|f_j\|_n=1$ (so $r_{n,j}=r$ and $f_{\max}=f_{\min}=1$) and $f=X\beta^*$. The event is measurable, does not depend on $\hat\beta_L$ or $\beta$, and the conclusions hold for every minimiser. $\phi_{\max}$ is the Rayleigh supremum of the model file.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 20, Lemma B.1, Eqs. (B.1)–(B.3), specialised to the linear model (7.1)–(7.2) of Section 7 as in the proof of Theorem 7.2, p. 28

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- Lemma B.1, p. 20, in the Section 7 specialisation used in the proof of Theorem 7.2
(unit diagonal, so `‖f_j‖_n = 1`, `f_max = f_min = 1`, `r_{n,j} = r`; target `f = Xβ*`).
With probability at least `1 − M^{1 − A²/8}`, every Lasso solution `β̂` satisfies
(B.1) simultaneously for all `β`, (B.2) and (B.3). -/
theorem lemma_B1 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X) (βstar : Fin M → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ,
        IsLasso X (fun i => X.mulVec βstar i + W i ω) r βhat →
        -- (B.1), for every β ∈ ℝ^M
        (∀ β : Fin M → ℝ,
          predLoss X (X.mulVec βstar) βhat + r * ∑ j, |βhat j - β j| ≤
              predLoss X (X.mulVec βstar) β + 4 * r * ∑ j ∈ supp β, |βhat j - β j| ∧
          predLoss X (X.mulVec βstar) β + 4 * r * ∑ j ∈ supp β, |βhat j - β j| ≤
              predLoss X (X.mulVec βstar) β +
                4 * r * Real.sqrt (sparsity β) *
                  Real.sqrt (∑ j ∈ supp β, (βhat j - β j) ^ 2)) ∧
        -- (B.2)
        (∀ j : Fin M,
          |(1 / (n : ℝ)) * ∑ i, X i j * (X.mulVec βstar i - X.mulVec βhat i)| ≤ 3 * r / 2) ∧
        -- (B.3)
        (sparsity βhat : ℝ) ≤ 4 * phiMax X * (predLoss X (X.mulVec βstar) βhat / r ^ 2) := by sorry

end LassoDantzig.Lasso
