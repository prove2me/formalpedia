-- Prove2me | Theorems.Thm_LassoDantzig_Equivalence_lemma_B3_eq_B10
-- name    : LassoDantzig.Equivalence.lemma_B3_eq_B10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:03:46.386386+00:00
-- url     : https://prove2.me/theorems/fabf8ab5-cb97-4143-9646-cbcf7298bfa0
-- title:
--   Lemma B.3, (B.10) — on $\mathcal B$, $|\frac1nX^\top(f-X\hat\beta_D)|_\infty\le 2rf_{\max}$
-- statement:
--   Let $n\ge1$, $M\ge2$, $X\in\mathbb R^{n\times M}$, $f,w\in\mathbb R^n$, $r>0$, and $y=f+w$. Suppose that the noise lies in the event $\mathcal B$:
--   $$
--   \Big|\frac1n\sum_{i=1}^nX_{ij}w_i\Big|\le r\|f_j\|_n\qquad(j=1,\dots,M),
--   $$
--   i.e. $\big|\tfrac1nD^{-1/2}X^\top w\big|_\infty\le r$. Then every Dantzig selector $\hat\beta_D$ for the data $y$ satisfies (B.10):
--   $$
--   \Big|\frac1nX^\top\big(f-X\hat\beta_D\big)\Big|_\infty\le2rf_{\max}.
--   $$
--
--   This is the (B.10) part of Lemma B.3, in the form its proof establishes ("(B.10) is satisfied on $\mathcal B$"); the paper bounds $\mathbb P(\mathcal B^c)\le M^{1-A^2/2}$ separately, and $\mathcal B\supseteq\mathcal A$. It is used in (B.11), the first half of the proof of Theorem 5.1.
--
--   **Formalization Note** Deterministic core of the probabilistic statement (B.10); the $\ell_\infty$ norm is written coordinatewise.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 23, Lemma B.3, Eq. (B.10) and its proof (event ℬ)

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- Lemma B.3, (B.10), on the event `ℬ`: if the noise `w` satisfies
`|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r` and `y = f + w`, every Dantzig selector `β̂_D` satisfies
`|(1/n) Xᵀ(f − Xβ̂_D)|_∞ ≤ 2 r f_max`. -/
theorem lemma_B3_eq_B10 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hw : NoiseEvent X r w) (βD : Fin M → ℝ) (hD : IsDantzig X (fun i => f i + w i) r βD) :
    ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (f i - X.mulVec βD i)| ≤ 2 * r * fmax X := by sorry

end LassoDantzig.Equivalence
