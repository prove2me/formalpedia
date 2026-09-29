-- Prove2me | Theorems.Thm_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq
-- name    : LT.LatticeTree.Vertex.isWithin_stdVertex_act_of_isInteger_of_det_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/5cac448a-f195-5ebe-9708-e2c80795370f
-- title:
--   Integral g moves the base vertex by at most v(det g)
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, with fraction field $K$ (an $R$-algebra realised as the localisation of $R$ at its nonzero elements), let $\varpi \in R$ be irreducible, and let $g$ be an element of $\mathrm{GL}_2(K)$, i.e. of the general linear group of $2\times 2$ matrices over $K$. Assume every entry $g_{ij}$ of $g$ lies in the image of $R$ in $K$ (`IsLocalization.IsInteger R`), and that for some natural number $k$ and some unit $u \in R^\times$ one has $\det g = u\,\varpi^{k}$ in $K$. Write $c \in K^\times$ for the unit $\varpi$ viewed in $K$ (nonzero since $\varpi \neq 0$ and $R \to K$ is injective). The conclusion is the relation `Vertex.IsWithin c k` between the standard vertex of the lattice tree, the homothety class of the lattice $L_0$ of vectors in $K^2$ with both coordinates integral, and its translate by $g$, the class of the image of $L_0$ under $v \mapsto g\,v$; unfolded, this says that there are finitely generated $R$-submodules $L, M$ of $K^2$ each spanning $K^2$ over $K$, with $L$ homothetic to $L_0$ and $M$ homothetic to $g L_0$, such that $c^{k} L \subseteq M \subseteq L$, i.e. $\varpi^{k} L \subseteq M \subseteq L$.
--
--   This is the easy inequality in the Cartan decomposition for $\mathrm{GL}_2$ over a local field: an integral matrix moves the base vertex of the tree of lattice classes a distance at most the valuation of its determinant. It is used for the bound on the distance between the standard vertex and its translate, and thence for the discreteness of the relevant group action on the $p$-adic upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LT.LatticeTree

theorem LT.LatticeTree.Vertex.isWithin_stdVertex_act_of_isInteger_of_det_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) k
      (LT.LatticeTree.stdVertex R K) (LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K)) := by sorry
