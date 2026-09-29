-- Prove2me | Theorems.Thm_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
-- name    : LT.LatticeTree.Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/e78c6886-20bc-51c0-ac93-865ee6e09017
-- title:
--   Unique neighbour towards v of a vertex at distance exactly n+1
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, $K$ a field which is an $R$-algebra and a fraction field of $R$, and let $\varpi \in R$ be irreducible; write $c = \varpi$ for the unit of $K$ obtained as the image of $\varpi$ under $\operatorname{algebraMap} R K$ (a unit since $\varpi \neq 0$), as produced by [`LT.LatticeTree.unitOfNeZero`](def/LatticeTreeOrbital.html#L505). Vertices of the tree are homothety classes of full lattices in $K^2$, a full lattice being a finitely generated $R$-submodule $L \subseteq K^2$ whose $K$-span is all of $K^2$; and for a natural number $m$, a vertex $w$ is within $m$ of a vertex $u$, written `IsWithin c m u w`, when $u$ and $w$ have full-lattice representatives $L$ and $M$ with $c^m L \subseteq M \subseteq L$. Let $v, x$ be vertices and $n$ a natural number, and assume $x$ is within $n+1$ of $v$ but not within $n$ of $v$. Then there is a vertex $y$ such that $y$ is within $1$ of $x$, $y$ is within $n$ of $v$, and every vertex $z$ within $1$ of $x$ with $z \neq x$ and $z \neq y$ fails to be within $n+1$ of $v$.
--
--   This is the statement that a vertex at distance exactly $n+1$ from $v$ in the Bruhat–Tits tree of $\mathrm{GL}_2$ over the fraction field of a discrete valuation ring has a single neighbour closer to $v$, all its other neighbours lying at distance $n+2$; the distances are measured in the scaling currency of the chosen uniformiser $\varpi$. It is used in the finiteness and cardinality computations for balls and twisted orbital sets in the tree, for instance in [`LT.LatticeTree.finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one`](thm.html#LT.LatticeTree.finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one) and [`LT.LatticeTree.twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap`](thm.html#LT.LatticeTree.twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
LT.LatticeTree.Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (v x : LT.LatticeTree.Vertex R K) (n : ℕ)
    (h : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v x)
    (h' : ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v x) :
    ∃ y : LT.LatticeTree.Vertex R K,
      LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x y ∧
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v y ∧
          ∀ z : LT.LatticeTree.Vertex R K,
            LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x z → z ≠ x → z ≠ y →
              ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v z := by sorry
