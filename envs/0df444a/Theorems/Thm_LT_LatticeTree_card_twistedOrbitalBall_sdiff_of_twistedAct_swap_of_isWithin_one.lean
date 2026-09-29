-- Prove2me | Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one
-- name    : LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/0a25643b-7b87-50c1-b374-fe3d7d9847c7
-- title:
--   Twisted displacement counts for an exchanged adjacent pair
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, let $\varpi \in R$ be irreducible and assume the residue ring $R/(\varpi)$ is finite; write $c = \varpi$ viewed as a unit of $K$ (`unitOfNeZero`). Let $\sigma$ be an `IntegralAut R K`, i.e. a ring automorphism of $K$ together with one of $R$ compatible with the structure map, let $\delta \in \mathrm{GL}_2(K)$, and consider the resulting twisted action $x \mapsto \delta \cdot \sigma(x)$ on the set of vertices, the homothety classes of finitely generated $R$-submodules of $K^2$ spanning $K^2$. Assume two vertices $x_0 \neq x_1$ satisfy: $x_0$ and $x_1$ are represented by full lattices $L \supseteq M \supseteq \varpi L$ (the relation `Vertex.IsWithin c 1`), and the twisted action sends $x_0$ to $x_1$ and $x_1$ to $x_0$. Then: (i) no vertex is fixed by the twisted action, $\mathrm{twistedFixedVertexSet}\,\delta\,\sigma = \emptyset$; (ii) for every $r$, the twisted ball of radius $2r+2$, i.e. $\{x : \mathrm{IsWithin}\ c\ (2r+2)\ x\ (\delta\cdot\sigma(x))\}$, coincides with that of radius $2r+1$, their difference being empty; and (iii) for every $r$ the difference of the twisted balls of radii $2r+1$ and $2r$ is finite, of cardinality $2\,|R/(\varpi)|^{\,r}$.
--
--   A counting statement on the Bruhat–Tits tree of $\mathrm{GL}_2$ over a local field: a twisted action that exchanges two adjacent vertices is an inversion, so it displaces every vertex by an odd amount, and the vertices displaced by exactly $2r+1$ number $2q^r$ for $q$ the residue cardinality. It feeds the evaluation of twisted orbital integrals, being cited by [`AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly) and [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime), and by the untwisted analogue [`LT.LatticeTree.card_orbitalBall_sdiff_of_act_swap_of_isWithin_one`](thm.html#LT.LatticeTree.card_orbitalBall_sdiff_of_act_swap_of_isWithin_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (x₀ x₁ : LT.LatticeTree.Vertex R K)
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (h₀ : LT.LatticeTree.Vertex.twistedAct δ σ x₀ = x₁)
    (h₁ : LT.LatticeTree.Vertex.twistedAct δ σ x₁ = x₀) :
    LT.LatticeTree.twistedFixedVertexSet δ σ = ∅ ∧
    (∀ r : ℕ,
        LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) δ σ).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ \
            LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) δ σ) =
        2 * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by sorry
