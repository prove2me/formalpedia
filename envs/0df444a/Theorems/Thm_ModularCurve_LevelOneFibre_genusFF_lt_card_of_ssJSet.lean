-- Prove2me | Theorems.Thm_ModularCurve_LevelOneFibre_genusFF_lt_card_of_ssJSet
-- name    : ModularCurve.LevelOneFibre.genusFF_lt_card_of_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/9a5ad503-a9ec-556a-88a9-90bded8b61ce
-- title:
--   Genus of X₀(q) is less than the number of supersingular j-invariants
-- statement:
--   Let $q$ be a prime, and let $k$ be an algebraically closed field of characteristic $q$. Let $S_0$ be a finite subset of $k$ whose elements are exactly the members of `ssJSet q k`, that is, those $j \in k$ such that every Weierstrass curve $W$ over $k$ which is elliptic and has $j$-invariant $j$ has no nonzero point $P$ on its associated affine curve with $q \cdot P = 0$ (so $j$ is the invariant only of curves with trivial $q$-torsion). Write $\overline{\mathbb{Q}}$ for `AlgebraicClosure ℚ` and let $F$ denote `modularFunctionFieldBar (1 * q)`: the intermediate field of the Laurent series field $\overline{\mathbb{Q}}((X))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull (1 * q)`, the latter being the subfield of $\mathbb{Q}((X))$ generated over $\mathbb{Q}$ by the divisor expansions of level $1 \cdot q$. The conclusion is the strict inequality $\mathrm{genusFF}(\overline{\mathbb{Q}}, F) < \#S_0$, where `genusFF` is the $\overline{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor of the function field $F$ over $\overline{\mathbb{Q}}$.
--
--   This is the comparison, for a prime $q$, between the genus of $X_0(q)$ and the number of supersingular $j$-invariants in characteristic $q$ (classically the two differ by exactly one, matching the Deligne–Rapoport description of the special fibre at $q$ as two rational curves crossing at the supersingular points). It serves as the non-speciality bound in the Riemann–Roch existence arguments for functions with prescribed orders and residues at places of the level-one fibre, cited by the `exists_mem_riemannRochSpace_…` results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelOneFibre_genusFF_lt_card_of_ssJSet.lean

import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_LevelOneComp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.LevelOneFibre.genusFF_lt_card_of_ssJSet
    {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) < S₀.card := by sorry
