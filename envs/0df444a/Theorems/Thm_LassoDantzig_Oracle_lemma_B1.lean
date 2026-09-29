-- Prove2me | Theorems.Thm_LassoDantzig_Oracle_lemma_B1
-- name    : LassoDantzig.Oracle.lemma_B1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:09:22.966156+00:00
-- url     : https://prove2.me/theorems/9f00efd1-6075-48d1-a0d7-6f04f26f0389
-- title:
--   Lemma B.1, (B.1) — basic inequality for the Lasso with high probability
-- statement:
--   Fix $M\ge2$ and $n\ge1$, a design $X\in\mathbb R^{n\times M}$ with nonzero column norms $\|f_j\|_n$ and an arbitrary target $f\in\mathbb R^n$. Let $W_1,\dots,W_n$ be independent $\mathcal N(0,\sigma^2)$ random variables with $\sigma^2>0$, $y=f+W$, and let $r=A\sigma\sqrt{\log M/n}$ for some $A>2\sqrt2$. Then there is an event of probability at least $1-M^{1-A^2/8}$ on which every Lasso solution $\hat\beta_L$ of (2.1), with $\hat f_L=X\hat\beta_L$, satisfies simultaneously for all $\beta\in\mathbb R^M$
--   $$\begin{aligned}\|\hat f_L-f\|_n^2+r\sum_{j=1}^M\|f_j\|_n|\hat\beta_{j,L}-\beta_j| &\le \|f_\beta-f\|_n^2+4r\sum_{j\in J(\beta)}\|f_j\|_n|\hat\beta_{j,L}-\beta_j|\\ &\le \|f_\beta-f\|_n^2+4r\sqrt{\mathcal M(\beta)}\Big(\sum_{j\in J(\beta)}\|f_j\|_n^2|\hat\beta_{j,L}-\beta_j|^2\Big)^{1/2}.\end{aligned}$$
--
--   Lemma B.1 is the common starting point of the paper's Lasso bounds (Theorems 5.1, 6.1, 7.2).
--
--   **Formalization Note** "With probability at least $1-M^{1-A^2/8}$" is a measurable event $E$ with $P(E)\ge1-M^{1-A^2/8}$, chosen before $\beta$ and the minimiser. Only the (B.1) clause of Lemma B.1 is stated; (B.2) and (B.3) are not used by Theorem 6.1.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 20, Lemma B.1, Eq. (B.1)

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Lemma B.1, (B.1)** (p. 20). Fix `M ≥ 2`, `n ≥ 1`, independent `W_i ∼ N(0, σ²)` with
`σ² > 0`, and `r = Aσ√(log M / n)` with `A > 2√2`. With probability at least `1 − M^{1−A²/8}`,
simultaneously for all `β ∈ ℝ^M` and every Lasso solution `β̂_L` of (2.1) with data `y = f + W`:
`‖f̂_L − f‖_n² + r ∑_j ‖f_j‖_n |β̂_{j,L} − β_j| ≤ ‖f_β − f‖_n² + 4r ∑_{j ∈ J(β)} ‖f_j‖_n |β̂_{j,L} − β_j|
  ≤ ‖f_β − f‖_n² + 4r √𝓜(β) √(∑_{j ∈ J(β)} ‖f_j‖_n² |β̂_{j,L} − β_j|²)`. -/
theorem lemma_B1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ, IsLasso X (fun i => f i + W i ω) (tuning n M A σ) βhat →
        ∀ β : Fin M → ℝ,
          empSq (fun i => X.mulVec βhat i - f i) +
                tuning n M A σ * ∑ j, colNorm X j * |βhat j - β j| ≤
              empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
            empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤
              empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * Real.sqrt (sparsity β) *
                  Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by sorry

end LassoDantzig.Oracle
