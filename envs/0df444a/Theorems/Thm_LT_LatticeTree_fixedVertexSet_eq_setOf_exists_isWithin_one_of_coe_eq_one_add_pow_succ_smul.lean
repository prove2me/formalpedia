-- Prove2me | Theorems.Thm_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_pow_succ_smul
-- name    : LT.LatticeTree.fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_pow_succ_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/67c270dd-a3b5-5dc0-9b45-75e2e77e9019
-- title:
--   Fixed vertices of 1+varpi^{j+1}Y as the 1-neighbourhood
-- statement:
--   Let $R$ be a discrete valuation ring that is a commutative domain, let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$, let $\varpi \in R$ be irreducible, let $Y$ be a $2\times 2$ matrix over $R$, and let $j$ be a natural number with $1 \le j$. Let $g, g'$ be elements of $\mathrm{GL}_2(K)$ whose underlying matrices are $1 + (\varpi)^j \cdot Y$ and $1 + (\varpi)^{j+1} \cdot Y$ respectively, all entries and scalars being taken in $K$ via the structure map $R \to K$. Vertices are homothety classes of full lattices in $K^2$, a full lattice being a finitely generated $R$-submodule of $K^2$ whose $K$-span is everything, and the fixed vertex set of an element of $\mathrm{GL}_2(K)$ consists of those classes left invariant by its action. The assertion is that the fixed vertex set of $g'$ coincides with the set of those vertices $x$ for which there exists a vertex $y$ fixed by $g$ with $x$ within $1$ of $y$ for the unit of $K$ given by the image of $\varpi$; explicitly, there are full lattices $L$ and $M$ representing $y$ and $x$ with $\varpi L \subseteq M \subseteq L$. Thus the fixed set of $g'$ is the closed $1$-neighbourhood, in the Bruhat–Tits tree, of the fixed set of $g$.
--
--   This is the neighbourhood law for fixed-point sets of congruence elements $1 + \varpi^j Y$ acting on the Bruhat–Tits tree of $\mathrm{GL}_2(K)$: passing from depth $j$ to depth $j+1$ replaces the fixed subtree by its closed ball of radius one. It is used in the computation of unit orbital counts ([`LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth`](thm.html#LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth)), where it yields the growth of the number of fixed vertices with the depth of the congruence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_pow_succ_smul.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_pow_succ_smul
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (Y : Matrix (Fin 2) (Fin 2) R) (j : ℕ) (hj : 1 ≤ j)
    (g g' : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = 1 + algebraMap R K ϖ ^ j • Y.map (algebraMap R K))
    (hg' : (g' : Matrix (Fin 2) (Fin 2) K) = 1 + algebraMap R K ϖ ^ (j + 1) • Y.map (algebraMap R K)) :
    LT.LatticeTree.fixedVertexSet (R := R) g' =
      {x | ∃ y ∈ LT.LatticeTree.fixedVertexSet (R := R) g,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 y x} := by sorry
