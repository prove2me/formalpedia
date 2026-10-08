-- Prove2me | Theorems.Thm_GivenDegreeSeq_MeanPolytope_expected_degree_eq_g
-- name    : GivenDegreeSeq.MeanPolytope.expected_degree_eq_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:36.664083+00:00
-- url     : https://prove2.me/theorems/c9ad4387-2e48-421c-abd4-dae887158f78
-- title:
--   Proof of Theorem 1.4, p. 15 — the expected degree of vertex i under P_x is g_i(x), so R is the range of g
-- statement:
--   Let $\mathbb P_x$ be the β-model law with parameter $x\in\mathbb R^n$, and let
--   $$g_i(x)=\sum_{j\neq i}\frac{e^{x_i+x_j}}{1+e^{x_i+x_j}},\qquad i=1,\dots,n.$$
--
--   Then, for every $x\in\mathbb R^n$ and every vertex $i$, the expected degree of vertex $i$ under $\mathbb P_x$ is
--   $$\mathbb E_x[d_i]=g_i(x).$$
--   Consequently the set $\mathcal R$ of expected degree sequences of the β-model equals the range $\{g(x):x\in\mathbb R^n\}$ of $g$.
--
--   This identity is what links the probabilistic definition of $\mathcal R$ to the analytic function $g$ studied in the rest of the proof of Theorem 1.4.
--
--   **Formalization Note** The expectation is the Bochner integral of the degree of vertex $i$ against $\mathbb P_x$ on the finite set of graphs on `Fin n`. The theorem has two conjuncts: the identity for every $x$ and $i$, and the set equality $\mathcal R=g(\mathbb R^n)$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 15, proof of Theorem 1.4

import Mathlib
import Definitions.Def_GivenDegreeSeq_MeanPolytope_Model

namespace GivenDegreeSeq.MeanPolytope

open MeasureTheory

/-- Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, proof of Theorem 1.4, p. 15: the expected degree of
vertex `i` under `P_x` is `g_i(x)`; hence `R` is the range of `g`. -/
theorem expected_degree_eq_g {n : ℕ} :
    (∀ (x : Fin n → ℝ) (i : Fin n), ∫ G, degSeq G i ∂ betaModel x = g x i) ∧
      R n = Set.range (g (n := n)) := by sorry

end GivenDegreeSeq.MeanPolytope
