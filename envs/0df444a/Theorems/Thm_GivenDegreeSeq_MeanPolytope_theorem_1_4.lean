-- Prove2me | Theorems.Thm_GivenDegreeSeq_MeanPolytope_theorem_1_4
-- name    : GivenDegreeSeq.MeanPolytope.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:53.23398+00:00
-- url     : https://prove2.me/theorems/abaca2fa-4853-45db-8b41-d45d880ba965
-- title:
--   Theorem 1.4 — the closure of the β-model expected degree sequences equals conv(D)
-- statement:
--   Fix $n$. For $\beta\in\mathbb R^n$ let $\mathbb P_\beta$ be the law of the β-model: the random simple graph on $\{1,\dots,n\}$ in which each pair $\{i,j\}$ is an edge independently with probability $e^{\beta_i+\beta_j}/(1+e^{\beta_i+\beta_j})$. Let
--   $$\mathcal R=\big\{(\mathbb E_\beta[d_1],\dots,\mathbb E_\beta[d_n]):\ \beta\in\mathbb R^n\big\}$$
--   be the set of expected degree sequences of the β-model, and let $\mathcal D$ be the set of all degree sequences of simple graphs on $n$ vertices. Then
--   $$\operatorname{conv}(\mathcal D)=\overline{\mathcal R},$$
--   where $\operatorname{conv}(\mathcal D)$ is the convex hull of $\mathcal D$ and $\overline{\mathcal R}$ is the topological closure of $\mathcal R$.
--
--   The theorem identifies, up to boundary, the vectors that arise as expected degree sequences of the β-model: no point of the degree-sequence polytope is left out. It is the mean-space result for this exponential family, and it is used in the paper's proof that the maximum likelihood estimator exists (Lemma 4.1).
--
--   **Formalization Note** The statement holds for every $n\ge 0$; for $n\le 1$ both sides are the single zero vector. $\mathcal R$ is defined through expectations under $\mathbb P_\beta$, not as the range of $g$. Closure is taken in `Fin n → ℝ`, whose product topology is the Euclidean topology. The equality cannot be strengthened to $\operatorname{conv}(\mathcal D)=\mathcal R$: the degree sequence $0$ of the empty graph is in $\mathcal D$ but is not the expected degree sequence of any β-model when $n\ge2$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 8, Theorem 1.4

import Mathlib
import Definitions.Def_GivenDegreeSeq_MeanPolytope_Model

namespace GivenDegreeSeq.MeanPolytope

/-- Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, Theorem 1.4, p. 8. Let `R` be the set of expected
degree sequences of the β-model `P_β` as `β` ranges over `ℝⁿ`, and `D` the set of degree sequences
of graphs on `n` vertices. Then `conv(D) = R̄`, the closure of `R`. -/
theorem theorem_1_4 (n : ℕ) : convexHull ℝ (D n) = closure (R n) := by sorry

end GivenDegreeSeq.MeanPolytope
