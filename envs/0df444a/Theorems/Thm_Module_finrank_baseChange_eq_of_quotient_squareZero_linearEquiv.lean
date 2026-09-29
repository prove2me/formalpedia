-- Prove2me | Theorems.Thm_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
-- name    : Module.finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/6aceb66c-1207-530c-b4ba-f95891b48fd0
-- title:
--   Constant rank descends along a square-zero quotient
-- statement:
--   Let $R$ be a commutative ring and $J \subseteq R$ an ideal with $J^2 = \bot$, let $S$ be a commutative ring and $\varphi \colon R/J \to S$ a ring isomorphism, let $P$ be an $S$-module and $P'$ an $R$-module (all carried by types in one fixed universe), and let $n$ be a natural number. Assume that $P$ has constant rank $n$ over $S$, in the sense that for every field $K$ equipped with an $S$-algebra structure one has $\dim_K(K \otimes_S P) = n$. Regard $P$ as an $R/J$-module by restricting its $S$-action along the ring homomorphism underlying $\varphi$ (the `Module.compHom` structure). The assertion is that any $R/J$-linear isomorphism $(R/J) \otimes_R P' \cong P$ forces $P'$ to have constant rank $n$ over $R$: for every field $K$ equipped with an $R$-algebra structure, $\dim_K(K \otimes_R P') = n$. Here $\dim_K$ is `Module.finrank`, so the conclusion is an equality of natural numbers, with the convention that non-finitely-generated (or infinite-rank) modules receive rank $0$.
--
--   This is the standard fact that the rank function of a module is detected by its reduction modulo a nilpotent ideal, here in the square-zero case and with the quotient identified with another ring along a prescribed isomorphism. It is used in the construction of rigidified line bundles over a square-zero thickening, in the verification that the candidate bundle has the expected rank on each chart of a two-chart affine open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct

set_option autoImplicit false

theorem Module.finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J ^ 2 = ⊥)
    {S : Type u} [CommRing S] (φ : R ⧸ J ≃+* S)
    (P : Type u) [AddCommGroup P] [Module S P]
    (P' : Type u) [AddCommGroup P'] [Module R P'] {n : ℕ}
    (hrk : ∀ (K : Type u) [Field K] [Algebra S K], Module.finrank K (K ⊗[S] P) = n) :
    letI : Module (R ⧸ J) P := Module.compHom P φ.toRingHom
    ((R ⧸ J) ⊗[R] P' ≃ₗ[R ⧸ J] P) →
    ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P') = n := by sorry
