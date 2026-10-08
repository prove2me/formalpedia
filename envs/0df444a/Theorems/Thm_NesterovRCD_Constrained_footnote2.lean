-- Prove2me | Theorems.Thm_NesterovRCD_Constrained_footnote2
-- name    : NesterovRCD.Constrained.footnote2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:44.597197+00:00
-- url     : https://prove2.me/theorems/fa98eaed-587d-4863-abb3-d9b5d79feebe
-- title:
--   Footnote 2 — under (2.2), strong convexity in $\|\cdot\|_1$ forces $\sigma\le1$
-- statement:
--   Let $\mathbb R^N=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_n}$ with $n\ge1$ and every $n_i\ge1$, each block carrying a Euclidean norm $\|\cdot\|_{(i)}$ (3.4). Let $f:\mathbb R^N\to\mathbb R$ have a coordinate-wise Lipschitz gradient (2.2) with constants $L_i>0$, and let $f$ be strongly convex in the norm $\|h\|_1^2=\sum_iL_i\|h^{(i)}\|_{(i)}^2$ of (3.5) with convexity parameter $\sigma>0$ (3.1). Then
--   $$\sigma\le1 .$$
--
--   In the proof of Theorem 5 this guarantees that $\beta=2\sigma/(1+\sigma)$ lies in $[0,1]$ and that the contraction factor $1-\frac{2\sigma}{n(1+\sigma)}$ of (4.6) is nonnegative.
--
--   **Formalization Note** The paper's blocks are $\mathbb R^{n_i}$ with $n_i\ge1$; Lean states this as nontriviality of every block space. It cannot be dropped: if every block were the zero space, every $\sigma$ would satisfy the hypotheses. Indices are `Fin n`, 0-based.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 14, footnote 2) (to the proof of Theorem 5)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Constrained_UCDM

namespace NesterovRCD.Constrained

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem footnote2 (hn : 0 < n) [∀ i, Nontrivial (E i)] (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hL : NesterovRCD.Sublinear.CoordLipschitz f L) (σ : ℝ) (hσ : 0 < σ) (hsc : NesterovRCD.HighProb.StronglyConvexW f L 1 σ) :
    σ ≤ 1 := by sorry

end NesterovRCD.Constrained
