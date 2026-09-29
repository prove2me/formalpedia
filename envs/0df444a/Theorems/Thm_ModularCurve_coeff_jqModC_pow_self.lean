-- Prove2me | Theorems.Thm_ModularCurve_coeff_jqModC_pow_self
-- name    : ModularCurve.coeff_jqModC_pow_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/1918cc1f-3da5-53c7-b67e-2a94e1e9e5f8
-- title:
--   The coefficient of q⁻ᵇ in j(q)ᵇ is 1
-- statement:
--   Let $K$ be a commutative ring and let $b$ be a natural number. Work in the Laurent series ring `LaurentSeries K`, realised as Hahn series over $\mathbb{Z}$ with coefficients in $K$. The element `jqModC K` is defined as the product of the Hahn series `HahnSeries.single (-1) 1`, i.e. $q^{-1}$, with the image under `HahnSeries.ofPowerSeries` of the power series `jNum` pushed forward along the canonical ring map $\mathbb{Z} \to K$, where `jNum` $=$ `eisenstein4`$^3\cdot$`dedekindEtaUnitInv` is the integral power series giving the holomorphic part of the $q$-expansion of the modular invariant. The theorem asserts that the coefficient of `jqModC K` raised to the power $b$ at the index $-(b : \mathbb{Z})$ equals $1$ in $K$. In other words, in $K((q))$ the $b$-th power of the reduction of the $j$-expansion has coefficient $1$ at $q^{-b}$; no hypothesis beyond commutativity of $K$ is imposed, and the case $b = 0$ is included.
--
--   This records the normalisation of the leading term of the $q$-expansion of the modular invariant $j = q^{-1} + 744 + \cdots$: its leading coefficient is $1$, hence a unit in every coefficient ring, and the same holds for all powers. It is used throughout the treatment of the models of the modular curves, for instance in the construction and comparison of prolongations of places where the order of vanishing of the $j$-function has to be computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_jqModC_pow_self.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_jqModC_pow_self (K : Type*) [CommRing K] (b : ℕ) :
    ((jqModC K) ^ b).coeff (-(b : ℤ)) = 1 := by sorry
