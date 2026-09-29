-- Prove2me | Theorems.Thm_IsLocalRing_isUnit_natCast_guardPrime_sub_one_of_charP_three
-- name    : IsLocalRing.isUnit_natCast_guardPrime_sub_one_of_charP_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/b9c86723-020a-56b2-93f4-1661d1fc81c9
-- title:
--   Units in a local ring: ℓ-1 when ℓ≡ 11 (mod 12) and residue characteristic 3
-- statement:
--   Let $R$ be a commutative ring which is local, and assume that its residue field has characteristic $3$. Let $\ell_g$ be a natural number which is prime and satisfies $\ell_g \bmod 12 = 11$. Then the image in $R$ of the natural number $\ell_g - 1$ (truncated subtraction in $\mathbb{N}$, followed by the canonical ring map $\mathbb{N} \to R$) is a unit of $R$. Since $\ell_g \equiv 11 \pmod{12}$ forces $\ell_g \geq 11$, the truncation is harmless and the element in question is the usual $\ell_g - 1$ times $1_R$; the congruence gives $\ell_g \equiv 2 \pmod 3$, so $\ell_g - 1$ is prime to the residue characteristic, which is exactly what invertibility in the local ring $R$ amounts to.
--
--   An elementary invertibility criterion of the form 'an integer prime to the residue characteristic is a unit in a local ring', specialised to residue characteristic $3$ and to an auxiliary ('guard') prime $\ell_g$ constrained modulo $12$. It is used in the construction of supersingular charts on modular curves of full level, where the order $\ell_g - 1$ of a group of diamond operators must be invertible in the local ring under consideration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isUnit_natCast_guardPrime_sub_one_of_charP_three.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.isUnit_natCast_guardPrime_sub_one_of_charP_three
    (R : Type*) [CommRing R] [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) 3]
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) :
    IsUnit ((ℓg - 1 : ℕ) : R) := by sorry
