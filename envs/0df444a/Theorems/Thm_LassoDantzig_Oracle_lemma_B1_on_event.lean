-- Prove2me | Theorems.Thm_LassoDantzig_Oracle_lemma_B1_on_event
-- name    : LassoDantzig.Oracle.lemma_B1_on_event
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:08:50.187186+00:00
-- url     : https://prove2.me/theorems/d0e62c3a-1a8d-4146-8e86-d66ba720f4f5
-- title:
--   Proof of Lemma B.1 — on the noise event every Lasso solution satisfies (B.1)
-- statement:
--   Let $n\ge1$, $X\in\mathbb R^{n\times M}$, $f,y\in\mathbb R^n$ and $r>0$, and suppose the noise vector $w=y-f$ lies in the event $\mathcal A$:
--   $$2\Big|\frac1n\sum_{i=1}^n X_{ij}w_i\Big|\le r\|f_j\|_n\qquad(j=1,\dots,M).$$
--   Let $\hat\beta$ be any Lasso solution (2.1) for the data $y$ with tuning constant $r$, and write $\hat f=X\hat\beta$. Then for every $\beta\in\mathbb R^M$
--   $$\begin{aligned}\|\hat f-f\|_n^2+r\sum_{j=1}^M\|f_j\|_n|\hat\beta_j-\beta_j| &\le \|X\beta-f\|_n^2+4r\sum_{j\in J(\beta)}\|f_j\|_n|\hat\beta_j-\beta_j|\\ &\le \|X\beta-f\|_n^2+4r\sqrt{\mathcal M(\beta)}\Big(\sum_{j\in J(\beta)}\|f_j\|_n^2|\hat\beta_j-\beta_j|^2\Big)^{1/2}.\end{aligned}$$
--
--   This deterministic "basic inequality" is the heart of the Lasso analysis; combined with (B.4) it gives Lemma B.1. The target $f$ is arbitrary.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 21, Appendix B, proof of Lemma B.1 ("so that on 𝒜 we get (B.1)")

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Lemma B.1, (B.1), deterministic core** (p. 21, proof of Lemma B.1: "so that on 𝒜 we get
(B.1)"). Let `w = y − f` lie in the event `𝒜`, i.e. `2|n⁻¹ ∑ᵢ X_{ij} w_i| ≤ r ‖f_j‖_n` for every
`j`, and let `β̂` be any Lasso solution (2.1) with tuning constant `r > 0`. Then for every
`β ∈ ℝ^M`:
`‖f̂_L − f‖_n² + r ∑_j ‖f_j‖_n |β̂_j − β_j| ≤ ‖f_β − f‖_n² + 4r ∑_{j ∈ J(β)} ‖f_j‖_n |β̂_j − β_j|
  ≤ ‖f_β − f‖_n² + 4r √𝓜(β) √(∑_{j ∈ J(β)} ‖f_j‖_n² |β̂_j − β_j|²)`. -/
theorem lemma_B1_on_event {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r) (hA : NoiseBound X (fun i => y i - f i) r)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ) :
    empSq (fun i => X.mulVec βhat i - f i) + r * ∑ j, colNorm X j * |βhat j - β j| ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      empSq (fun i => X.mulVec β i - f i) +
          4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * Real.sqrt (sparsity β) *
            Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by sorry

end LassoDantzig.Oracle
