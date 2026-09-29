-- Prove2me | Theorems.Thm_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct
-- name    : LT.LatticeTree.nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/75f7f08b-afe0-5422-ac26-9ea8f5b5575d
-- title:
--   Fixed vertex or swapped pair for a twisted tree action
-- statement:
--   Let $R$ be a discrete valuation ring with field of fractions $K$ (a commutative domain, an $R$-algebra $K$ which is a fraction field of $R$), let $\varpi \in R$ be irreducible, let $\sigma$ be an `IntegralAut R K`, that is a ring automorphism of $K$ together with a ring automorphism of $R$ compatible with the structure map $R \to K$, let $\delta \in \mathrm{GL}_2(K)$, and let $m \ge 1$ be a natural number. Vertices are homothety classes of full lattices, i.e. finitely generated $R$-submodules of $K^2$ spanning $K^2$ over $K$, and `Vertex.twistedAct δ σ` sends the class of $L$ to the class of $\delta\,\sigma(L)$. Assume that the $m$-th iterate of `Vertex.twistedAct δ σ` either fixes some vertex, or interchanges two distinct vertices $x_0 \ne x_1$ admitting representing lattices $L, M$ with $\varpi L \subseteq M \subseteq L$ (the relation `Vertex.IsWithin` for the unit $\varpi \in K^\times$ and exponent $1$). Then the map `Vertex.twistedAct δ σ` itself either has a fixed vertex, so that `twistedFixedVertexSet δ σ` is nonempty, or interchanges two distinct vertices satisfying the same relation $\varpi L \subseteq M \subseteq L$. Which of the two alternatives holds is not asserted.
--
--   This is the descent from an iterate to the map itself for a $\sigma$-twisted action on the Bruhat–Tits tree of $\mathrm{GL}_2(K)$, in the form of the classical fixed-point theorem for automorphisms of trees (a fixed vertex or an inverted edge). It is used by the untwisted statement [`LT.LatticeTree.nonempty_fixedVertexSet_or_exists_swap_of_iterate_act`](thm.html#LT.LatticeTree.nonempty_fixedVertexSet_or_exists_swap_of_iterate_act) and in the computation of twisted orbital integrals and the matching of Hecke operators at an inert prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (m : ℕ) (hm : 1 ≤ m)
    (h : (∃ x : LT.LatticeTree.Vertex R K, (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x = x) ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x₀ = x₁ ∧ (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x₁ = x₀) :
    (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          LT.LatticeTree.Vertex.twistedAct δ σ x₀ = x₁ ∧ LT.LatticeTree.Vertex.twistedAct δ σ x₁ = x₀ := by sorry
