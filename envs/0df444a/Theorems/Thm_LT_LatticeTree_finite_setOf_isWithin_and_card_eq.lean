-- Prove2me | Theorems.Thm_LT_LatticeTree_finite_setOf_isWithin_and_card_eq
-- name    : LT.LatticeTree.finite_setOf_isWithin_and_card_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/0a0ec4fa-fee9-5206-835b-604824c30dab
-- title:
--   Finiteness and size of balls of radius d in the lattice tree
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$, let $\varpi \in R$ be an irreducible element, and assume the residue ring $R/\varpi R$ is finite; let $v$ be a vertex of the lattice tree of $R$ in $K$, that is, a homothety class of full lattices in $K^2$ (a full lattice being a finitely generated $R$-submodule $L \subseteq K^2$ whose $K$-span is all of $K^2$), and let $d \in \mathbb{N}$. Write $c \in K^\times$ for the image of $\varpi$ under $R \to K$ (a unit since $\varpi \neq 0$). Consider the set of vertices $w$ for which [`LT.LatticeTree.Vertex.IsWithin`](def/LatticeTreeBaseChange.html#L274) holds with parameters $c$ and $d$, i.e. there are full lattices $L, M \subseteq K^2$ whose homothety classes are $v$ and $w$ respectively and which satisfy $c^{d} L \subseteq M \subseteq L$. The assertion is that this set is finite and that, with $q = \#(R/\varpi R)$, its cardinality equals $$1 + \sum_{r < d} (q+1)\,q^{r}.$$
--
--   This is the count of the ball of radius $d$ about a vertex in the Bruhat–Tits tree of $\mathrm{GL}_2$ over the fraction field of a discrete valuation ring with finite residue field of size $q$, the tree being $(q+1)$-regular; for $d = 0$ the ball is the single vertex $v$. It is used for the corresponding finiteness statement for the distance function on the Bruhat–Tits tree, for counts of vertices outside a twisted fixed-point set, and in the verification that a certain group action is discrete.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_finite_setOf_isWithin_and_card_eq.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.finite_setOf_isWithin_and_card_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (v : LT.LatticeTree.Vertex R K) (d : ℕ) :
    ({w : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) d v w}).Finite ∧
    Nat.card ↥({w : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) d v w}) =
      1 + ∑ r ∈ Finset.range d, (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by sorry
