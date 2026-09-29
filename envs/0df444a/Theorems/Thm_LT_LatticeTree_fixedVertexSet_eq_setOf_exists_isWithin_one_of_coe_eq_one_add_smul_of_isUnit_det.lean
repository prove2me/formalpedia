-- Prove2me | Theorems.Thm_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_smul_of_isUnit_det
-- name    : LT.LatticeTree.fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_smul_of_isUnit_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/0390cc38-03d3-5964-b765-cb9adc5e286e
-- title:
--   Vertices fixed by 1+varpi Y neighbour those fixed by b+Y
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (via a fixed $R$-algebra structure making $K$ the fraction field), let $\varpi \in R$ be irreducible, let $Y$ be a $2\times 2$ matrix over $R$ and $b \in R$, and assume that $\det(b\cdot 1 + Y)$ is a unit of $R$. Let $g, g' \in \mathrm{GL}_2(K)$ be such that $g$ has matrix $b\cdot 1 + Y$ and $g'$ has matrix $1 + \varpi Y$, both entries being taken under $R \to K$. Vertices here are homothety classes of full lattices, that is, of finitely generated $R$-submodules $L \subseteq K^2$ with $K\cdot L = K^2$, and the fixed-vertex set of an element of $\mathrm{GL}_2(K)$ consists of the classes it carries to themselves. The conclusion is that the set of vertices fixed by $g'$ equals the set of vertices $x$ for which there is a vertex $y$ fixed by $g$ with $x$ within one step of $y$, in the sense that $y$ and $x$ admit full-lattice representatives $L$ and $M$ with $\varpi L \le M \le L$, where $\varpi$ acts through its image, a unit of $K$. No congruence condition on $Y$ modulo $\varpi$ is imposed.
--
--   This is the level-zero case of the neighbourhood law for fixed-vertex sets on the tree of $\mathrm{GL}_2$ over a local field: passing from $b + Y$ to $1 + \varpi Y$ replaces the fixed set by its closed ball of radius one. It serves as the base case of the recursion counting fixed vertices of $1 + \varpi^{j}Y$, and is used in [`LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth`](thm.html#LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_smul_of_isUnit_det.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.fixedVertexSet_eq_setOf_exists_isWithin_one_of_coe_eq_one_add_smul_of_isUnit_det
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (Y : Matrix (Fin 2) (Fin 2) R) (b : R)
    (hdet : IsUnit (b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).det)
    (g g' : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K b • 1 + Y.map (algebraMap R K))
    (hg' : (g' : Matrix (Fin 2) (Fin 2) K) = 1 + algebraMap R K ϖ • Y.map (algebraMap R K)) :
    LT.LatticeTree.fixedVertexSet (R := R) g' =
      {x | ∃ y ∈ LT.LatticeTree.fixedVertexSet (R := R) g,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 y x} := by sorry
