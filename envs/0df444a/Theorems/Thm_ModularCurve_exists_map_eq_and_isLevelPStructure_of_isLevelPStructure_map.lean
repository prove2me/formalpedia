-- Prove2me | Theorems.Thm_ModularCurve_exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map
-- name    : ModularCurve.exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/d7aeba92-68f3-5845-baa8-9331fb6e4e27
-- title:
--   Level-ℓ structures over K descend to the valuation ring
-- statement:
--   Let $R_0$ be a discrete valuation domain with field of fractions $K$ (the field structure and fraction-field identification being part of the hypotheses), let $W_0$ be a Weierstrass curve over $R_0$ whose discriminant $\Delta$ is a unit of $R_0$, and let $\ell$ be a prime whose image in $R_0$ is a unit. A datum of level $\ell$ over a commutative ring $A$, in the sense of [`ModularCurve.LevelPData`](def/ModularCurve_KatzLevelP.html#L43), is a quadruple $(x_P,y_P,x_Q,y_Q)$ of elements of $A$, and `map` transports such a quadruple along a ring homomorphism componentwise. The predicate [`ModularCurve.IsLevelPStructure W p D`](def/ModularCurve_KatzLevelP.html#L104) asserts six things: $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$; the polynomial $W.\mathrm{pre}\Psi_p$ vanishes at $x_P$ and at $x_Q$; and both independence elements $\prod_{a=1}^{(p-1)/2}\bigl(x\cdot(W.\Psi\mathrm{Sq}_a)(x_0)-(W.\Phi_a)(x_0)\bigr)$, taken with $(x_0,x)=(x_P,x_Q)$ and with $(x_0,x)=(x_Q,x_P)$, are units. Given a level-$\ell$ datum $D'$ over $K$ which is a level-$\ell$ structure on the base change $W_0\otimes_{R_0}K$, the conclusion is that there exists a level-$\ell$ datum $D_0$ over $R_0$ whose componentwise image under the structure map $R_0\to K$ equals $D'$ and which is itself a level-$\ell$ structure on $W_0$.
--
--   This is the statement that a $\Gamma(\ell)$-structure on the generic fibre of a Weierstrass model with unit discriminant over a discrete valuation ring, for $\ell$ invertible in the ring, is already defined over the ring — the integrality of the coordinates of $\ell$-torsion points together with the injectivity of reduction on $\ell$-torsion, which upgrades the non-vanishing of the independence elements over $K$ to their invertibility over $R_0$. It is used in the construction of integral models of level structures on modular curves, in particular in the lifting arguments over discrete valuation rings and in the comparison of level structures with Weierstrass models having prescribed $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (hΔ₀ : IsUnit W₀.Δ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (D' : ModularCurve.LevelPData K) (hD' : ModularCurve.IsLevelPStructure (W₀.map (algebraMap R₀ K)) ℓ D') :
    ∃ D₀ : ModularCurve.LevelPData R₀, D₀.map (algebraMap R₀ K) = D' ∧ ModularCurve.IsLevelPStructure W₀ ℓ D₀ := by sorry
