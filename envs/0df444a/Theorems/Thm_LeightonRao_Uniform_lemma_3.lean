-- Prove2me | Theorems.Thm_LeightonRao_Uniform_lemma_3
-- name    : LeightonRao.Uniform.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:01.176595+00:00
-- url     : https://prove2.me/theorems/76264a42-abc3-482e-ade6-a4877407d961
-- title:
--   Lemma 3, p. 797 — partition into components of radius ≤ Δ cutting at most 4W log n/Δ capacity
-- statement:
--   Let $G$ be any network on $n$ nodes with arbitrary capacities, let $d$ be a distance function with total weight $W$, and let $\Delta>0$. Then $V$ can be partitioned into components, each of radius at most $\Delta$, such that the total capacity of the edges connecting nodes in different components is at most
--   $$\frac{4W\log n}{\Delta}.$$
--   Here $\log n=\log_2 n$.
--
--   This region-growing decomposition is the main combinatorial tool of the paper: it trades the radius of the pieces against the capacity cut between them.
--
--   **Formalization Note** The radius is measured inside the component: each component has a centre from which every node of the component is reached by a walk inside the component of $d$-length at most $\Delta$. No connectivity of $G$ and no lower bound on $n$ is assumed, as on the page ("any graph G").
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 797, Lemma 3

import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Lemma 3, p. 797: a bounded-radius partition with controlled crossing capacity. -/
theorem lemma_3 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, HasRadiusLE N d S Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d * Real.logb 2 (Fintype.card V : ℝ) / Δ := by sorry

end LeightonRao.Uniform
