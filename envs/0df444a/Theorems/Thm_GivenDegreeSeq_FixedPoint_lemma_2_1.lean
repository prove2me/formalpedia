-- Prove2me | Theorems.Thm_GivenDegreeSeq_FixedPoint_lemma_2_1
-- name    : GivenDegreeSeq.FixedPoint.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:33.670052+00:00
-- url     : https://prove2.me/theorems/ea071dbb-740f-435d-b8d8-bbf9314254e7
-- title:
--   Lemma 2.1 — $|AB|_\infty\le1-2(n-2)\delta^2/(n-1)$ for $A,B\in\mathcal L_n(\delta)$
-- statement:
--   Let $n\ge2$ and $\delta>0$. Say that an $n\times n$ real matrix $A=(a_{ij})$ belongs to $\mathcal L_n(\delta)$ if $|A|_\infty=\max_i\sum_j|a_{ij}|\le1$ and, for each $1\le i\ne j\le n$, $a_{ii}\ge\delta$ and $a_{ij}\le-\delta/(n-1)$. If $A,B\in\mathcal L_n(\delta)$, then
--   $$|AB|_\infty\le1-\frac{2(n-2)\delta^2}{n-1}.$$
--
--   For $n\ge3$ the right-hand side is strictly less than $1$, so although each factor has operator norm at most $1$, the product of two such matrices is a strict contraction in the $L^\infty$ operator norm. This is the key tool for the geometric convergence of the fixed-point iteration for the $\beta$-model MLE.
--
--   **Formalization Note** $|\cdot|_\infty$ is the maximal absolute row sum, which equals the $L^\infty$ operator norm. The hypothesis $n\ge2$ makes $n-1>0$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 11, Lemma 2.1

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_ClassLn

namespace GivenDegreeSeq.FixedPoint

/-- Lemma 2.1, p. 11: if `A, B ∈ L_n(δ)` then `|AB|∞ ≤ 1 − 2(n − 2)δ²/(n − 1)`. -/
theorem lemma_2_1 {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : classLn n δ A) (hB : classLn n δ B) :
    matNormInf (A * B) ≤ 1 - 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) := by sorry

end GivenDegreeSeq.FixedPoint
