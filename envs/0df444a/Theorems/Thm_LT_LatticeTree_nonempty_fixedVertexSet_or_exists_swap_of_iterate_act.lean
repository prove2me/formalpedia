-- Prove2me | Theorems.Thm_LT_LatticeTree_nonempty_fixedVertexSet_or_exists_swap_of_iterate_act
-- name    : LT.LatticeTree.nonempty_fixedVertexSet_or_exists_swap_of_iterate_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/d41cd6fe-6a68-533c-ab6f-95dfc9a74e59
-- title:
--   Fixed vertex or swapped adjacent pair descends from an iterate
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, let $\varpi \in R$ be irreducible, and let $g \in \mathrm{GL}_2(K)$. Here a vertex is a homothety class of full lattices in $K^2$, a full lattice being a finitely generated $R$-submodule $L \subseteq K^2$ whose $K$-span is all of $K^2$, and $g$ acts on vertices by $L \mapsto g\cdot L$ (the image of $L$ under $v \mapsto g v$), which is well defined on homothety classes. For vertices $x_0, x_1$, the relation `Vertex.IsWithin` with parameters $c = \varpi \in K^\times$ and $n = 1$ asserts the existence of full lattices $L, M$ representing $x_0, x_1$ with $\varpi L \subseteq M \subseteq L$. Assume $m \ge 1$ and that the $m$-th iterate of the action of $g$ either fixes some vertex, or interchanges two distinct vertices $x_0 \ne x_1$ standing in the relation above. Then either the set of vertices fixed by $g$ itself is nonempty, or there are two distinct vertices $x_0 \ne x_1$ in that same relation which $g$ itself interchanges: $g\cdot x_0 = x_1$ and $g\cdot x_1 = x_0$. Which of the two alternatives holds is not asserted.
--
--   This is the descent step for the action of $\mathrm{GL}_2(K)$ on the Bruhat–Tits tree of $\mathrm{SL}_2$ over a discrete valuation ring: an element an iterate of which has a fixed vertex, or inverts an edge, already fixes a vertex or inverts an edge. It feeds the computation of orbital integrals and the construction of matching Hecke operators in the automorphic part of the argument, being cited by [`AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly`](thm.html#AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly), its twisted counterpart, and [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_nonempty_fixedVertexSet_or_exists_swap_of_iterate_act.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.nonempty_fixedVertexSet_or_exists_swap_of_iterate_act
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (m : ℕ) (hm : 1 ≤ m)
    (h : (∃ x : LT.LatticeTree.Vertex R K, (LT.LatticeTree.Vertex.act g)^[m] x = x) ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          (LT.LatticeTree.Vertex.act g)^[m] x₀ = x₁ ∧ (LT.LatticeTree.Vertex.act g)^[m] x₁ = x₀) :
    (LT.LatticeTree.fixedVertexSet (R := R) g).Nonempty ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          LT.LatticeTree.Vertex.act g x₀ = x₁ ∧ LT.LatticeTree.Vertex.act g x₁ = x₀ := by sorry
