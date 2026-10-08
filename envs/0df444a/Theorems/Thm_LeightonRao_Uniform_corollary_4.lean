-- Prove2me | Theorems.Thm_LeightonRao_Uniform_corollary_4
-- name    : LeightonRao.Uniform.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:56.067414+00:00
-- url     : https://prove2.me/theorems/cfb5666f-e628-49ee-8f0c-03e0da0c7dbc
-- title:
--   Corollary 4, pp. 798–799 — a component of radius 1/2n² with ≥ 2n/3 nodes, or a cut of ratio cost ≤ 36W log n
-- statement:
--   Let $G$ be a network on $n\ge2$ nodes and $d$ a distance function with total weight $W$. Then at least one of the following holds:
--
--   1. there is a set $T$ of at least $2n/3$ nodes with radius at most $1/(2n^2)$;
--   2. there is a nonempty proper subset $U\subset V$ whose ratio cost satisfies
--   $$\frac{C(U,\bar U)}{|U|\,|\bar U|}\le 36\,W\log n .$$
--
--   Corollary 4 applies Lemma 3 with $\Delta=1/(2n^2)$; it is the case split on which Lemma 6 is built.
--
--   **Formalization Note** The page states case (2) as "ratio cost $O(W\log n)$"; the constant $36$ is the one computed in the proof on p. 799 ($8Wn^2\log n/((2n/3)(n/3))=36W\log n$). "Find a component" is stated as the existence of a vertex set $T$ with the stated size and radius; Lemma 6 uses only these two properties. $n\ge2$ is assumed because a one-node graph has no proper cut. Algorithmic content ("we can find") is not formalized.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 798–799, Corollary 4 (constant 36 from its proof, p. 799)

import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Corollary 4, pp. 798–799, with the proof's explicit factor `36`. -/
theorem corollary_4 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V)
    (d : V → V → ℝ) (hd : IsDistanceFunction d) :
    (∃ T : Finset V,
      2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ) ∧
      HasRadiusLE N d T (1 / (2 * (Fintype.card V : ℝ) ^ 2))) ∨
    (∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      ratioCost N U ≤ 36 * totalWeight N d * Real.logb 2 (Fintype.card V : ℝ)) := by sorry

end LeightonRao.Uniform
