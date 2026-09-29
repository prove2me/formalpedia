-- Prove2me | Theorems.Thm_LT_LatticeTree_card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
-- name    : LT.LatticeTree.card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/db2e24d2-e444-510f-963e-022459f2bc39
-- title:
--   Displacement sphere counts on the lattice tree for g with finite non-empty fixed set
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (the fraction-field structure being part of the data), let $\varpi \in R$ be irreducible and assume the residue ring $R/(\varpi)$ is finite; write $q = \#\,R/(\varpi)$ and let $c \in K^\times$ be the unit [`LT.LatticeTree.unitOfNeZero`](def/LatticeTreeOrbital.html#L505) attached to $\varpi \neq 0$, namely the image of $\varpi$ under $R \to K$. Let $g \in \mathrm{GL}_2(K)$ and consider the vertex set [`LT.LatticeTree.Vertex R K`](def/LatticeTreeOrbital.html#L349) of homothety classes of full $R$-lattices in $K^2$, with the action of $g$. Put $F = \{v : g\cdot v = v\}$ (`fixedVertexSet`), assumed finite and non-empty, and $C = \#F$ (`unitOrbitalCount`). For $n \in \mathbb{N}$, `orbitalBall c n g` is the set of vertices $x$ such that $x$ and $g\cdot x$ have lattice representatives $L$, $M$ with `LatticeWithin c n L M`. The assertion is twofold: first, for every $r$, `orbitalBall c (2*r+1) g \ orbitalBall c (2*r) g` is empty; second, for every $r$, the set `orbitalBall c (2*r+2) g \ orbitalBall c (2*r+1) g` is finite of cardinality exactly $(C\,(q-1)+2)\,q^{r}$, the subtraction $q-1$ being truncated subtraction in $\mathbb{N}$.
--
--   This is the counting of displacement spheres for an element of $\mathrm{GL}_2(K)$ acting on the tree of homothety classes of lattices: the displacement function takes only even values, and the sphere of displacement $2r+2$ has $(C(q-1)+2)q^{r}$ vertices, where $C$ is the number of fixed vertices. It feeds the computation of orbital integrals and the comparison of local Hecke operators, being cited by [`AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly`](thm.html#AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly), [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime) and [`LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth`](thm.html#LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (LT.LatticeTree.fixedVertexSet (R := R) g).Finite)
    (hne : (LT.LatticeTree.fixedVertexSet (R := R) g).Nonempty) :
    (∀ r : ℕ,
        LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) g = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) g \
            LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g) =
        (LT.LatticeTree.unitOrbitalCount R g * (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) + 2) *
          Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by sorry
