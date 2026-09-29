-- Prove2me | Theorems.Thm_LassoDantzig_Equivalence_lemma_B1_eq_B2
-- name    : LassoDantzig.Equivalence.lemma_B1_eq_B2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:56:52.785326+00:00
-- url     : https://prove2.me/theorems/4f540c47-3f83-4cd8-ae34-12d5b6c162e8
-- title:
--   Lemma B.1, (B.2) — on $\mathcal A$, $|\frac1nX^\top(f-X\hat\beta_L)|_\infty\le 3rf_{\max}/2$
-- statement:
--   Let $n\ge1$, $M\ge2$, $X\in\mathbb R^{n\times M}$, $f,w\in\mathbb R^n$ and $r>0$, and let the observations be $y=f+w$. Suppose that the noise lies in the event $\mathcal A$, that is,
--   $$
--   2\Big|\frac1n\sum_{i=1}^nX_{ij}w_i\Big|\le r\,\|f_j\|_n\qquad(j=1,\dots,M),
--   $$
--   equivalently (B.5): $\big|\tfrac1nD^{-1/2}X^\top w\big|_\infty\le r/2$. Then every Lasso solution $\hat\beta_L$ (a minimiser of (2.1) for the data $y$) satisfies (B.2):
--   $$
--   \Big|\frac1nX^\top\big(f-X\hat\beta_L\big)\Big|_\infty\le\frac{3rf_{\max}}{2},
--   $$
--   where $f_{\max}=\max_j\|f_j\|_n$.
--
--   Together with (B.4), which gives $\mathbb P(\mathcal A)\ge1-M^{1-A^2/8}$ for $r=A\sigma\sqrt{\log M/n}$, this is the (B.2) part of Lemma B.1 of the paper. It controls the correlation of the Lasso's residual with the dictionary and is used in the half (B.16)–(B.17) of the proof of Theorem 5.1.
--
--   **Formalization Note** The statement is the deterministic core of Lemma B.1 (B.2): it holds for every noise vector in $\mathcal A$, which is how the paper's proof uses it ("To prove (B.2) it suffices to note that on $\mathcal A$ we have (B.5)"). The $\ell_\infty$ norm is written coordinatewise.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 20, Lemma B.1, Eq. (B.2); p. 21, proof of Lemma B.1, Eq. (B.5)

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- Lemma B.1, (B.2), on the event `𝒜`: if the noise `w` lies in `𝒜` (i.e. (B.5),
`|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r/2`) and `y = f + w`, every Lasso solution `β̂_L` satisfies
`|(1/n) Xᵀ(f − Xβ̂_L)|_∞ ≤ 3 r f_max / 2`. -/
theorem lemma_B1_eq_B2 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hw : NoiseEventHalf X r w) (βL : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βL) :
    ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (f i - X.mulVec βL i)| ≤ 3 * r * fmax X / 2 := by sorry

end LassoDantzig.Equivalence
