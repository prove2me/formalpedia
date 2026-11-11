-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_3_1
-- name    : OptimalLCA.Matching.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:46:52.734924+00:00
-- url     : https://prove2.me/theorems/4590690d-215f-4865-a1dc-73e3b379ea68
-- title:
--   Lemma 3.1 — saddle-point value 4ν_f(G) − n
-- statement:
--   For a graph $G$ on $n$ vertices with $Q$, $X$, $P$, $F$ as in §3:
--   (a) $P(q)\le2\nu_f(G)$ for every $q\in Q$;
--   (b) $\min_{x\in X}F(x,q)=2P(q)-n$ for every $q\in Q$;
--   (c) there is $q^*\in Q$ with $F(x,q^*)\ge4\nu_f(G)-n$ for every $x\in X$, in which each vertex puts all its mass on a single neighbour or on its dummy;
--   (d) $$\min_{x\in X}\max_{q\in Q}F(x,q)=\max_{q\in Q}\min_{x\in X}F(x,q)=4\nu_f(G)-n.$$
--   This is the min–max formulation whose value the optimizer of §5 approximates.
--
--   Differences from the source:
--   - encoding: index set I = {(u,a) : a ∈ N(u) ∪ {⊥_u}} → V ⊕ G.Dart (dummy coordinates and ordered edges); reason: same coordinates
--   - encoding: min and max in (b) and (d) → IsLeast / IsGreatest of the value sets (outer and inner optima attained); reason: states attainment as the paper's min/max do
--   - encoding: each vertex puts all of its mass on a single neighbor or on its dummy → every block of q* has a coordinate equal to 1; reason: with q* ≥ 0 and block sums 1, this is all mass on that coordinate
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), pp. 14–15, Lemma 3.1

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Graph
import Definitions.Def_OptimalLCA_Matching_SaddlePoint

namespace OptimalLCA.Matching

/-- Lemma 3.1 (saddle-point value). For every graph `G` on `n` vertices:
(a) `P(q) ≤ 2 ν_f(G)` for every `q ∈ Q`;
(b) `min_{x ∈ X} F(x, q) = 2P(q) - n` for every `q ∈ Q`;
(c) some `q* ∈ Q` puts all of each vertex's mass on a single neighbour or on its dummy and
has `F(x, q*) ≥ 4 ν_f(G) - n` for every `x ∈ X`;
(d) `min_{x ∈ X} max_{q ∈ Q} F(x, q) = max_{q ∈ Q} min_{x ∈ X} F(x, q) = 4 ν_f(G) - n`
(every `min`/`max` attained). -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (∀ q, InQ G q → acceptedMass G q ≤ 2 * fracMatchingNumber G) ∧
    (∀ q, InQ G q →
      IsLeast {r : ℝ | ∃ x, InX x ∧ objF G x q = r}
        (2 * acceptedMass G q - (Fintype.card V : ℝ))) ∧
    (∃ qs : Idx G → ℝ, InQ G qs ∧
      (∀ x, InX x → 4 * fracMatchingNumber G - (Fintype.card V : ℝ) ≤ objF G x qs) ∧
      ∀ u : V, ∃ i : Idx G, owner i = u ∧ qs i = 1) ∧
    (IsLeast {r : ℝ | ∃ x, InX x ∧ IsGreatest {s : ℝ | ∃ q, InQ G q ∧ objF G x q = s} r}
        (4 * fracMatchingNumber G - (Fintype.card V : ℝ)) ∧
      IsGreatest {r : ℝ | ∃ q, InQ G q ∧ IsLeast {s : ℝ | ∃ x, InX x ∧ objF G x q = s} r}
        (4 * fracMatchingNumber G - (Fintype.card V : ℝ))) := by sorry

end OptimalLCA.Matching
