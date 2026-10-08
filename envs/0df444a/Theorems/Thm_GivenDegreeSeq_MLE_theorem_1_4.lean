-- Prove2me | Theorems.Thm_GivenDegreeSeq_MLE_theorem_1_4
-- name    : GivenDegreeSeq.MLE.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:18.947453+00:00
-- url     : https://prove2.me/theorems/b609cd9e-1310-4539-b8df-5b40726e6aee
-- title:
--   Theorem 1.4 — $\mathrm{conv}(\mathcal D)=\overline{\mathcal R}$
-- statement:
--   Let $\mathcal R\subseteq\mathbb R^n$ be the set of expected degree sequences $(\mathbb E_\beta d_1,\dots,\mathbb E_\beta d_n)$ of the $\beta$-model $\mathbb P_\beta$ as $\beta$ ranges over $\mathbb R^n$, and let $\mathcal D\subseteq\mathbb R^n$ be the set of degree sequences of simple graphs on $n$ vertices. Then for every $n$,
--   $$\mathrm{conv}(\mathcal D)=\overline{\mathcal R},$$
--   where $\mathrm{conv}$ is the convex hull and $\overline{\mathcal R}$ the topological closure in $\mathbb R^n$.
--
--   No degree sequence is left out: every point of the degree-sequence polytope is a limit of $\beta$-model expected degree sequences. In this mission it is the input that places every observed degree sequence in $\overline{\mathcal R}$, so that Lemma 4.1 applies to it.
--
--   **Formalization Note** This restates the goal of mission 2 of the series in this mission's namespace (drafts cannot import drafts); it is to be replaced by a reference item once that mission is published.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 8, Theorem 1.4

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_BetaModel

namespace GivenDegreeSeq.MLE

/-- Theorem 1.4, p. 8. For every `n`, the convex hull of the set `D` of degree sequences of
simple graphs on `n` vertices equals the topological closure of the set `R` of expected degree
sequences of the β-model `P_β`, `β ∈ ℝⁿ`. -/
theorem theorem_1_4 (n : ℕ) : convexHull ℝ (D n) = closure (R n) := by sorry

end GivenDegreeSeq.MLE
