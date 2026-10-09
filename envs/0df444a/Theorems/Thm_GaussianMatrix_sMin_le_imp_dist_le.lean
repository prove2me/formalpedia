-- Prove2me | Theorems.Thm_GaussianMatrix_sMin_le_imp_dist_le
-- name    : GaussianMatrix.sMin_le_imp_dist_le
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:51:02.851244+00:00
-- url     : https://prove2.me/theorems/338965c8-e146-4b2e-b9e4-5a494c343744
-- title:
--   Small $\sigma_{\min}$ forces a column close to the span of the others: $\sigma_{\min}(A)\le s\Rightarrow \exists j,\ \operatorname{dist}(a_j,H_j)\le\sqrt n\, s$
-- statement:
--   Let $A$ be a real $N\times n$ matrix with $n\ge 1$, with columns $a_1,\dots,a_n\in\mathbb R^N$, and let
--   $$\sigma_{\min}(A)=\inf_{x\in\mathbb R^n,\ \|x\|_2=1}\|Ax\|_2$$
--   be its smallest singular value. For a column index $j$ let $H_j=\operatorname{span}\{a_i: i\ne j\}$, and write
--   $$\operatorname{dist}(a_j,H_j)=\inf_{x\in\mathbb R^n,\ x_j=1}\|Ax\|_2=\inf_{c}\Big\|a_j+\sum_{i\neq j}c_i a_i\Big\|_2 .$$
--   If $\sigma_{\min}(A)\le s$ for a real number $s$, then there is a column index $j$ with
--   $$\operatorname{dist}(a_j,H_j)\;\le\;\sqrt n\; s .$$
--
--   Indeed, for every unit vector $x$ choose $j$ with $|x_j|=\max_i|x_i|$, so that $|x_j|\ge n^{-1/2}$; then $x/x_j$ has $j$-th entry $1$ and $\operatorname{dist}(a_j,H_j)\le \|Ax\|/|x_j|\le\sqrt n\|Ax\|$. Hence $\min_j\operatorname{dist}(a_j,H_j)\le\sqrt n\,\sigma_{\min}(A)\le\sqrt n\,s$.
--
--   This deterministic "invertibility via distance" reduction reduces small-ball estimates for the smallest singular value of a random matrix to small-ball estimates for the distance of a single random column to a subspace spanned by the remaining (independent) columns.
--
--   **Formalization Note.** $\sigma_{\min}$ is `GaussianMatrix.sMin`, with $\|v\|_2$ written as `Real.sqrt (v ⬝ᵥ v)`. The distance is expressed without a separate definition as the infimum of $\|Ax\|_2$ over vectors $x$ with $x_j=1$ (an infimum of a nonnegative family over a nonempty index set, so no `sInf ∅` issue arises).
-- source:
--   M. Rudelson, R. Vershynin, "The Littlewood–Offord problem and invertibility of random matrices", Adv. Math. 218 (2008), proof of Lemma 3.5 (the inequality ‖Ax‖ ≥ |x_j| dist(a_j, H_j), eq. (3.7)).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem sMin_le_imp_dist_le {N n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin N) (Fin n) ℝ) (s : ℝ)
    (hs : sMin A ≤ s) :
    ∃ j : Fin n, (⨅ x : {x : Fin n → ℝ // x j = 1}, Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)))
      ≤ Real.sqrt n * s := by sorry

end GaussianMatrix
