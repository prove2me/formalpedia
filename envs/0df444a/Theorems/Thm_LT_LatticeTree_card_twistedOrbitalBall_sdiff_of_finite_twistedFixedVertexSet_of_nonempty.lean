-- Prove2me | Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty
-- name    : LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/9ab93b46-6dfb-5d29-a1ad-7ec661c21a40
-- title:
--   Twisted displacement shells on the tree for a finite non-empty twisted fixed set
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, $K$ a field which is an $R$-algebra and a fraction field of $R$, $\varpi \in R$ an irreducible element, and assume the residue ring $R/(\varpi)$ is finite; write $q = \#(R/(\varpi))$. Let $\sigma$ be an `IntegralAut R K`, i.e. a ring automorphism of $K$ together with a ring automorphism of $R$ compatible with the structure map $R \to K$, and let $\delta \in \mathrm{GL}_2(K)$. Vertices are homothety classes of full $R$-lattices in $K^2$, and the twisted action sends a vertex $x$ to $\delta \cdot \sigma(x)$. Assume the set of vertices fixed by this twisted action is finite and non-empty, and let $C$ be its cardinality (`twistedUnitOrbitalCount`). For $n \in \mathbb{N}$, `twistedOrbitalBall` of radius $n$ (measured in the scaling unit given by the image of $\varpi$ in $K^\times$) is the set of vertices $x$ admitting full-lattice representatives $L$ of $x$ and $M$ of $\delta \cdot \sigma(x)$ with `LatticeWithin` at level $n$. The assertion is twofold: first, for every $r$ the ball of radius $2r+1$ minus the ball of radius $2r$ is empty; second, for every $r$ the ball of radius $2r+2$ minus the ball of radius $2r+1$ is finite, of cardinality $(C(q-1)+2)\,q^{r}$, the subtraction $q-1$ being in $\mathbb{N}$.
--
--   This is the twisted displacement count on the Bruhat–Tits tree of $\mathrm{GL}_2(K)$: no vertex is displaced an odd amount by $x \mapsto \delta\cdot\sigma(x)$, and the vertices displaced exactly $2r+2$ form a shell whose size grows by the factor $q$ at each step, with leading constant determined by the number of twisted-fixed vertices. It feeds the evaluation of twisted orbital integrals and the construction of matching Hecke operators at an inert prime, and the untwisted analogue is deduced from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (LT.LatticeTree.twistedFixedVertexSet δ σ).Finite)
    (hne : (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty) :
    (∀ r : ℕ,
        LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) δ σ = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) δ σ \
            LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ) =
        (LT.LatticeTree.twistedUnitOrbitalCount δ σ * (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) + 2) *
          Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by sorry
