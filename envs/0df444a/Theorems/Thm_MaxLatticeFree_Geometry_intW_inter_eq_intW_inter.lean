-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_intW_inter_eq_intW_inter
-- name    : MaxLatticeFree.Geometry.intW_inter_eq_intW_inter
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:21:35.741461+00:00
-- url     : https://prove2.me/theorems/65b2ef37-cde1-4f56-ac3b-5e1c13c07ca6
-- title:
--   Eq. (6) — relative interiors commute with intersecting a subspace
-- statement:
--   Let $V\subseteq W$ be linear subspaces of $\mathbb R^n$ and let $S\subseteq W$ be convex. If the interior of $S$ relative to $W$ meets $V$, that is $\mathbf{int}_W(S)\cap V\neq\emptyset$, then
--
--   $$
--   \mathbf{int}_W(S)\cap V=\mathbf{int}_V(S\cap V).
--   $$
--
--   This identity (6) lets the proof of Theorem 9 transfer lattice-freeness between $S\subseteq W$ and its trace $S\cap V$ on the subspace that carries the lattice.
--
--   **Formalization Note** In the paper (6) is claimed inside Case 2 of the proof of Theorem 9, where $S$ is moreover a full-dimensional maximal $\Lambda$-free convex set of $W$. The proof of (6) on p. 9 uses only convexity of $S\subseteq W$, $V\subseteq W$, and $\mathbf{int}_W(S)\cap V\neq\emptyset$, so only these are assumed.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 9, Eq. (6) (Case 2 in the proof of Theorem 9)

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_intW

namespace MaxLatticeFree.Geometry

theorem intW_inter_eq_intW_inter {n : ℕ} (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hVW : V ≤ W)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSW : S ⊆ (W : Set (EuclideanSpace ℝ (Fin n)))) (hS : Convex ℝ S)
    (hne : (intW (W : Set (EuclideanSpace ℝ (Fin n))) S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    intW (W : Set (EuclideanSpace ℝ (Fin n))) S ∩ (V : Set (EuclideanSpace ℝ (Fin n))) =
      intW (V : Set (EuclideanSpace ℝ (Fin n))) (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) := by sorry

end MaxLatticeFree.Geometry
