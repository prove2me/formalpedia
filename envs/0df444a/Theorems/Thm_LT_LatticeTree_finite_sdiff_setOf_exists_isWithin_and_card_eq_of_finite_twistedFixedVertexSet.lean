-- Prove2me | Theorems.Thm_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet
-- name    : LT.LatticeTree.finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/861fa8f0-c910-5c20-a4e9-7b8fc8a59e0e
-- title:
--   Vertices at distance exactly r+1 from a twisted fixed set
-- statement:
--   Let $R$ be a discrete valuation domain with field of fractions $K$, let $\varpi \in R$ be irreducible, and assume the residue ring $R/(\varpi)$ is finite; write $q = \mathrm{Nat.card}(R/(\varpi))$. Vertices are homothety classes of full lattices in $K^2$, i.e. of finitely generated $R$-submodules $L \subseteq K^2$ with $K\cdot L = K^2$, and for the unit $c = \varpi \in K^\times$ the relation `Vertex.IsWithin` $c\,n\,f\,x$ means that $f$ and $x$ have representatives $L$ and $M$ with $\varpi^n L \subseteq M \subseteq L$. Let $\sigma$ be an `IntegralAut R K`, that is a ring automorphism of $K$ together with a ring automorphism of $R$ compatible with the structure map $R \to K$, and let $\delta \in \mathrm{GL}_2(K)$. Let $F = \{v \mid \mathrm{Vertex.twistedAct}\ \delta\ \sigma\ v = v\}$ be the set of vertices fixed by the twisted action, assumed finite and non-empty, and put $C = \mathrm{Nat.card}\,F$. Then for every $r \in \mathbb{N}$ the set of vertices within $r+1$ of some member of $F$ but not within $r$ of any member of $F$ is finite, of cardinality exactly $(C(q-1)+2)\,q^r$, the subtraction being truncated subtraction of naturals.
--
--   This is the count of vertices lying at distance exactly $r+1$ from the fixed subtree of a twisted action of $\mathrm{GL}_2(K)\rtimes\mathrm{Aut}$ on the Bruhat–Tits tree of a discrete valuation ring: the fixed set, being a finite subtree with $C$ vertices, has exactly $C(q-1)+2$ edges leaving it, and each such edge carries $q^r$ vertices at distance $r+1$. It feeds the computation of the cardinality of the corresponding balls minus the fixed set in [`LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty`](thm.html#LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (LT.LatticeTree.twistedFixedVertexSet δ σ).Finite)
    (hne : (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty) (r : ℕ) :
    ({x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (r + 1) f x} \
        {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r f x}).Finite ∧
    Nat.card ↥({x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (r + 1) f x} \
        {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r f x}) =
      (Nat.card ↥(LT.LatticeTree.twistedFixedVertexSet δ σ) * (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) + 2) *
        Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by sorry
