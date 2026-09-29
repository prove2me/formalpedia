-- Prove2me | Theorems.Thm_ModularCurve_exists_map_eq_and_isGamma1Point_of_isGamma1Point_map
-- name    : ModularCurve.exists_map_eq_and_isGamma1Point_of_isGamma1Point_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/dfd58dd9-9dec-54f1-b006-02d366bce9c1
-- title:
--   Γ₁(ℓ)-points of the generic fibre descend to R₀
-- statement:
--   Let $R_0$ be an integrally closed integral domain and $K$ a field which is a fraction field of $R_0$ (both in the same universe), let $W_0$ be a Weierstrass curve over $R_0$, and let $\ell$ be a natural number whose image in $R_0$ is a unit. Let $D'$ be a level-$P$ datum over $K$, that is, a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $K$, and suppose that $D'$ is a $\Gamma_1$-point of the base change $W_0 \otimes_{R_0} K$ at level $\ell$ in the sense of the project predicate [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10): the pair $(x_P, y_P)$ satisfies the affine Weierstrass equation of $W_0 \otimes_{R_0} K$, the division polynomial $\mathrm{pre}\Psi_\ell$ of that curve vanishes at $x_P$, and moreover $x_Q = x_P$ and $y_Q = y_P$. The conclusion is that there is a level-$P$ datum $D_0$ over $R_0$, i.e. a quadruple of elements of $R_0$, whose coordinatewise image under $R_0 \to K$ equals $D'$ and which is itself a $\Gamma_1$-point of $W_0$ at level $\ell$ in the same sense.
--
--   This is the statement that a $\Gamma_1(\ell)$-structure on the generic fibre of an integral Weierstrass model is already defined over the base, for $\ell$ invertible; it rests on the integrality of the coordinates of $\ell$-torsion points. It is used in the treatment of level structures on Weierstrass models, notably by [`WeierstrassCurve.exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range`](thm.html#WeierstrassCurve.exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range) and by the two statements about the rigid data attached to $H^1$-type level packages at a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_map_eq_and_isGamma1Point_of_isGamma1Point_map.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.exists_map_eq_and_isGamma1Point_of_isGamma1Point_map
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (D' : ModularCurve.LevelPData K) (hD' : ModularCurve.IsGamma1Point (W₀.map (algebraMap R₀ K)) ℓ D') :
    ∃ D₀ : ModularCurve.LevelPData R₀, D₀.map (algebraMap R₀ K) = D' ∧ ModularCurve.IsGamma1Point W₀ ℓ D₀ := by sorry
