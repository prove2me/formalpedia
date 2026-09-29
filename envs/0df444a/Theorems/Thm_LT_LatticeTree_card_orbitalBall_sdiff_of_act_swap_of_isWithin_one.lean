-- Prove2me | Theorems.Thm_LT_LatticeTree_card_orbitalBall_sdiff_of_act_swap_of_isWithin_one
-- name    : LT.LatticeTree.card_orbitalBall_sdiff_of_act_swap_of_isWithin_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/2862d850-4a5b-5bcd-9dcc-94a816013228
-- title:
--   Displacement counts for a GL₂ class swapping two adjacent vertices
-- statement:
--   Let $R$ be a discrete valuation domain with field of fractions $K$ (the algebra structure making $K$ the fraction field of $R$), let $\varpi \in R$ be irreducible and assume the residue ring $R/(\varpi)$ is finite. Write $c \in K^\times$ for the image of $\varpi$ under [`LT.LatticeTree.unitOfNeZero`](def/LatticeTreeOrbital.html#L505), and recall that a vertex is a homothety class of full lattices, i.e. of finitely generated $R$-submodules of $K^2$ spanning $K^2$ over $K$, and that `Vertex.act` is induced by $L \mapsto gL$. Let $g \in \mathrm{GL}_2(K)$ and let $x_0, x_1$ be vertices such that: `Vertex.IsWithin` holds for $c$, $n = 1$ and the pair $(x_0,x_1)$, that is, there are full lattices $L \ni$ representing $x_0$ and $M$ representing $x_1$ with $\varpi L \subseteq M \subseteq L$; $x_0 \neq x_1$; and $g \cdot x_0 = x_1$, $g \cdot x_1 = x_0$. Then: (i) `fixedVertexSet g` is empty, i.e. no vertex satisfies $g \cdot v = v$; (ii) for every $r \in \mathbb{N}$ the difference of the orbital balls of radii $2r+2$ and $2r+1$ for $c$ and $g$ is empty, where `orbitalBall c n g` is the set of vertices $x$ with `IsWithin c n x (g \cdot x)`; and (iii) for every $r$ the difference of the orbital balls of radii $2r+1$ and $2r$ is finite, of cardinality $2 \cdot \#(R/(\varpi))^r$.
--
--   This is the displacement count on the Bruhat–Tits tree of $\mathrm{GL}_2(K)$ for an element acting as an inversion of an edge: it has no fixed vertex, all displacements are odd, and exactly $2q^r$ vertices are displaced by $2r+1$, where $q$ is the residue cardinality. It is used in the computation of orbital integrals attached to elements with irreducible characteristic polynomial and in the construction of matching Hecke operators at an inert prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_card_orbitalBall_sdiff_of_act_swap_of_isWithin_one.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.card_orbitalBall_sdiff_of_act_swap_of_isWithin_one
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (x₀ x₁ : LT.LatticeTree.Vertex R K)
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (h₀ : LT.LatticeTree.Vertex.act g x₀ = x₁) (h₁ : LT.LatticeTree.Vertex.act g x₁ = x₀) :
    LT.LatticeTree.fixedVertexSet (R := R) g = ∅ ∧
    (∀ r : ℕ,
        LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) g).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g \
            LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) g) =
        2 * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by sorry
