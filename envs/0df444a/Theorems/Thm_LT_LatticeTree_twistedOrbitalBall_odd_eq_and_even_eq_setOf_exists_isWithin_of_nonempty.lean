-- Prove2me | Theorems.Thm_LT_LatticeTree_twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
-- name    : LT.LatticeTree.twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/a3e1918d-3196-5dd3-a61f-9269101998f4
-- title:
--   Odd twisted orbital balls collapse; even ones surround the fixed set
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (via a fixed $R$-algebra structure making $K$ the fraction field), let $\varpi \in R$ be irreducible, and write $c =$ [`LT.LatticeTree.unitOfNeZero`](def/LatticeTreeOrbital.html#L505) for the image of $\varpi$ in $K^\times$. Vertices are homothety classes of full lattices, i.e. of finitely generated $R$-submodules of $K^2$ spanning $K^2$ over $K$, and for $n \in \mathbb{N}$ a vertex $v$ is within $n$ of a vertex $w$ when they have representatives $L$, $M$ with $c^n L \subseteq M \subseteq L$. Let $\sigma$ be an `IntegralAut R K`, that is, a ring automorphism of $K$ together with one of $R$ compatible under the algebra map, let $\delta \in \mathrm{GL}_2(K)$, and let $x \mapsto \delta \cdot \sigma(x)$ be the resulting twisted action on vertices; the $n$-th twisted orbital ball is the set of vertices $x$ within $n$ of $\delta \cdot \sigma(x)$. Assume the set of vertices fixed by the twisted action is non-empty, and let $m \in \mathbb{N}$. Then the ball of radius $2m+1$ equals the ball of radius $2m$, and the ball of radius $2m$ is exactly the set of vertices $x$ for which some twisted-fixed vertex $f$ is within $m$ of $x$.
--
--   This is the tree-theoretic statement that an isometry with a fixed vertex displaces every vertex by exactly twice its distance to the fixed set, formulated for the twisted action of $\delta\sigma$ on the Bruhat–Tits tree of $\mathrm{GL}_2$ over a discrete valuation ring, with distances measured in powers of the chosen uniformiser. It is used in the counting of twisted orbital balls and of unit orbital counts, where the cardinality of the difference of successive balls is computed from the fixed set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hne : (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty) (m : ℕ) :
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m + 1) δ σ =
      LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
          (2 * m) δ σ ∧
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m) δ σ =
      {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m f x} := by sorry
