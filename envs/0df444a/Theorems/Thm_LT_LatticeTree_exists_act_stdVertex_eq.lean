-- Prove2me | Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
-- name    : LT.LatticeTree.exists_act_stdVertex_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/24ff6f28-0885-589f-af6f-0734807035d0
-- title:
--   GL₂(K) acts transitively on lattice-tree vertices
-- statement:
--   Let $R$ be a commutative ring that is a domain and a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$. Here a vertex, an element of [`LT.LatticeTree.Vertex R K`](def/LatticeTreeOrbital.html#L349), is a class of pairs consisting of a submodule $L \subseteq K^2$ (with $K^2$ realised as `Fin 2 → K`) satisfying the predicate `IsFullLattice`, taken modulo the relation `Homothetic` on the underlying submodules, which in the present setting amounts to $L'$ being the image of $L$ under a scalar matrix $\mathrm{scalarGL}(c)$ for some $c \in K^\times$; the standard vertex `stdVertex R K` is the class of the standard lattice, the submodule of those $v \in K^2$ both of whose coordinates lie in the image of $R$, and $g \in \mathrm{GL}_2(K)$ acts on a class by sending the representative $L$ to its image $g\cdot L$ under the $R$-linear map $x \mapsto g \,*ᵥ\, x$. The assertion is that for every vertex $v$ there exists $g \in \mathrm{GL}_2(K)$ with $g \cdot (\text{standard vertex}) = v$; that is, the action of $\mathrm{GL}_2(K)$ on the vertex set is transitive, the standard vertex being a base point. No uniformiser of $R$ and no hypothesis on its residue field enter.
--
--   This is the standard transitivity statement underlying the description of the Bruhat–Tits tree of $\mathrm{SL}_2$ over a local field: the vertex set is a single $\mathrm{GL}_2(K)$-orbit, so every vertex may be moved to the homothety class of the standard lattice. It is used in the development of lattice trees and in the analysis of Mumford-type quotients and period data for curves built on that development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_exists_act_stdVertex_eq.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.exists_act_stdVertex_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : LT.LatticeTree.Vertex R K) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K,
      LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K) = v := by sorry
