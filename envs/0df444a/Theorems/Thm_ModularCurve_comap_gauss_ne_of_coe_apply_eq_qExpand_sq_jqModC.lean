-- Prove2me | Theorems.Thm_ModularCurve_comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC
-- name    : ModularCurve.comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/df2d243d-f43a-5243-ab20-306fbf132778
-- title:
--   Scaling j by q² moves the Gauss valuation ring
-- statement:
--   Let $q$ be a prime, $L$ a field of characteristic zero, and $K$ an intermediate field between $L$ and the field $\mathrm{LaurentSeries}\,L$ of formal Laurent series over $L$. Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, and assume $q$ lies in the maximal ideal of $A$. Let $W_0$ be a valuation subring of $K$ satisfying the following explicit description: an element $f$ of $K$ lies in $W_0$ exactly when there are power series $x,y$ over $A$ with the reduction of $y$ modulo the maximal ideal of $A$ nonzero, such that, as Laurent series over $L$, $f$ times the image of $y$ equals the image of $x$ (the images being taken along $A \to L$). Let $\varphi$ be an $L$-algebra automorphism of $K$, and let $j \in K$ have Laurent expansion $\mathrm{jqModC}\,L$, that is $t^{-1}$ times the image over $L$ of the integral power series $\mathrm{jNum} = \mathrm{eisenstein4}^3 \cdot \mathrm{dedekindEtaUnitInv}$. Assume the Laurent expansion of $\varphi(j)$ is obtained from $\mathrm{jqModC}\,L$ by the ring homomorphism $\mathrm{qExpand}\,L\,(q^2)$, which multiplies every exponent by $q^2$. Then the pullback of $W_0$ along $\varphi$ is not equal to $W_0$.
--
--   This is the separating witness for the Gauss valuation subring attached to the branch at infinity: an $L$-automorphism of the function field that rescales the formal parameter on $j$ by $q^2$ cannot preserve the ring of ratios of $q$-integral power series with unit denominator. It is used in [`ModularCurve.FullLevel.comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply`](thm.html#ModularCurve.FullLevel.comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply) to identify which level automorphisms stabilise that valuation subring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC
    (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (φ : ↥K ≃ₐ[L] ↥K)
    (j : ↥K) (hj : (j : LaurentSeries L) = ModularCurve.jqModC L)
    (hφj : ((φ j : ↥K) : LaurentSeries L) = ModularCurve.qExpand L (q ^ 2) (ModularCurve.jqModC L)) :
    W₀.comap φ.toAlgHom.toRingHom ≠ W₀ := by sorry
