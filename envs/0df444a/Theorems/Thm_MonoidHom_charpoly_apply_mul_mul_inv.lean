-- Prove2me | Theorems.Thm_MonoidHom_charpoly_apply_mul_mul_inv
-- name    : MonoidHom.charpoly_apply_mul_mul_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/bad5c08f-fc90-5d85-86d7-3a3977b6724d
-- title:
--   Conjugation invariance of characteristic polynomials of a representation
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module which is free and finite over $R$, and $G$ a group. Let $\rho : G \to \mathrm{End}_R(M)$ be a monoid homomorphism, i.e. a linear representation of $G$ on $M$ (multiplicative on products and sending $1$ to the identity endomorphism). Then for all $\sigma, \tau \in G$ the characteristic polynomials of the endomorphisms $\rho(\tau\sigma\tau^{-1})$ and $\rho(\sigma)$ of $M$ coincide as elements of $R[X]$: $(\rho(\tau\sigma\tau^{-1})).\mathrm{charpoly} = (\rho(\sigma)).\mathrm{charpoly}$, where the characteristic polynomial of an endomorphism of a finite free module is the one computed from its matrix in any basis. No hypothesis of nonzero rank, of local or Noetherian nature, or of continuity is imposed; the rank of $M$ is arbitrary.
--
--   This is the similarity invariance of the characteristic polynomial, in the form that says the characteristic polynomial of $\rho(g)$ depends only on the conjugacy class of $g$. It is used in the Galois-theoretic parts of the argument to make conditions on the characteristic polynomial of a Frobenius or of an inertia element independent of the choice of the element within its conjugacy class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_charpoly_apply_mul_mul_inv.lean

import Mathlib.LinearAlgebra.Charpoly.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MonoidHom.charpoly_apply_mul_mul_inv {R : Type*} {M : Type*} {G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Group G] (ρ : G →* Module.End R M) (σ τ : G) : (ρ (τ * σ * τ⁻¹)).charpoly = (ρ σ).charpoly := by sorry
