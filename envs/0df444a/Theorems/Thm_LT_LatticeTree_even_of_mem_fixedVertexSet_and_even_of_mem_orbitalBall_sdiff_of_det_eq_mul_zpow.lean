-- Prove2me | Theorems.Thm_LT_LatticeTree_even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
-- name    : LT.LatticeTree.even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/089d9be8-4489-5d63-8802-1a607e2c9bfb
-- title:
--   Parity of vertex displacement equals parity of orddet
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $\varpi \in R$ be irreducible. Let $g \in \mathrm{GL}_2(K)$, let $k \in \mathbb{Z}$ and $u \in R^\times$, and suppose $\det g = \iota(u)\,\iota(\varpi)^k$ in $K$, where $\iota$ is the structure map $R \to K$. Write $\mathrm{Vertex}\,R\,K$ for the quotient of the full $R$-lattices in $K^2$ by homothety, and let $c = \iota(\varpi)$, viewed as a unit of $K$ via `unitOfNeZero`. Two assertions are made. First, if some vertex $x$ lies in `fixedVertexSet` $g$, i.e. satisfies $\mathrm{act}\,g\,x = x$, then $k$ is even. Second, for every natural number $n$ and every vertex $x$ lying in `orbitalBall` $c\,(n+1)\,g$ but not in `orbitalBall` $c\,n\,g$ — that is, there are full lattices $L, M$ whose homothety classes are $x$ and $\mathrm{act}\,g\,x$ with `LatticeWithin` $c\,(n+1)\,L\,M$ holding, while no such pair exists at level $n$ — the integer $(n+1) - k$ is even.
--
--   This records the parity constraint on the displacement of a vertex of the Bruhat–Tits tree of $\mathrm{GL}_2$ over a discrete valuation ring: the distance from $x$ to $g\cdot x$ is congruent modulo $2$ to the valuation of $\det g$, in the form needed for counting fixed vertices and spheres. It is used in the computation of (twisted) orbital integrals and in the construction of matching Hecke operators at an inert prime, via [`AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly`](thm.html#AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly), [`AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly) and [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (k : ℤ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    (∀ x : LT.LatticeTree.Vertex R K, x ∈ LT.LatticeTree.fixedVertexSet (R := R) g → Even k) ∧
    ∀ (n : ℕ) (x : LT.LatticeTree.Vertex R K),
      x ∈
        LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n) g →
      Even ((n : ℤ) + 1 - k) := by sorry
