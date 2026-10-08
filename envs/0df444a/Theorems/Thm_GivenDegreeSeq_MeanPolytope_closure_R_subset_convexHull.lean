-- Prove2me | Theorems.Thm_GivenDegreeSeq_MeanPolytope_closure_R_subset_convexHull
-- name    : GivenDegreeSeq.MeanPolytope.closure_R_subset_convexHull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:25.181139+00:00
-- url     : https://prove2.me/theorems/d201fbda-102a-4286-b7ae-addea5f563e7
-- title:
--   Proof of Theorem 1.4, p. 15 — conv(D) ⊇ R̄
-- statement:
--   Let $\mathcal D\subseteq\mathbb R^n$ be the set of degree sequences of simple graphs on $n$ vertices, and let $\mathcal R\subseteq\mathbb R^n$ be the set of expected degree sequences of the β-model $\mathbb P_\beta$ as $\beta$ ranges over $\mathbb R^n$. Then the closure of $\mathcal R$ lies in the convex hull of $\mathcal D$:
--   $$\overline{\mathcal R}\subseteq\operatorname{conv}(\mathcal D).$$
--
--   This is the easy inclusion of Theorem 1.4: every expected degree sequence is a weighted average of degree sequences.
--
--   **Formalization Note** The closure is taken in `Fin n → ℝ` with the product topology, which is the Euclidean topology of $\mathbb R^n$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 15, proof of Theorem 1.4

import Mathlib
import Definitions.Def_GivenDegreeSeq_MeanPolytope_Model

namespace GivenDegreeSeq.MeanPolytope

/-- Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, proof of Theorem 1.4, p. 15: `conv(D) ⊇ R̄`. -/
theorem closure_R_subset_convexHull (n : ℕ) : closure (R n) ⊆ convexHull ℝ (D n) := by sorry

end GivenDegreeSeq.MeanPolytope
