-- Prove2me | Theorems.Thm_ModularCurve_delta_tateLaurent
-- name    : ModularCurve.delta_tateLaurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/44e31bb2-ed8c-598d-ae40-71d54b6d5814
-- title:
--   Discriminant of the Tate curve equals qprod(1-qⁿ)²⁴
-- statement:
--   Let $K$ be a commutative ring. Consider the Weierstrass curve `tateLaurent K` over the field of Laurent series `LaurentSeries K`: it is the base change of the integral Weierstrass curve `tatePowerSeries` $=\langle 1,0,0,\mathrm{tateA4},\mathrm{tateA6}\rangle$ over `PowerSeries ℤ` along the ring homomorphism `laurentOfInt K`, which applies the coefficientwise map induced by $\mathbb{Z}\to K$ and then the inclusion `HahnSeries.ofPowerSeries` of power series into Laurent (Hahn) series. The assertion is that the discriminant $\Delta$ of this curve is the Laurent series attached in the same way to the integral power series $X\cdot \mathrm{dedekindEtaUnit}$, where `dedekindEtaUnit` is the twenty-fourth power of `etaProd` $=\prod_{n\ge 0}\bigl(1-X^{n+1}\bigr)$; that is, writing $q$ for the Laurent variable, $$\Delta\bigl(\mathrm{tateLaurent}\ K\bigr)=q\prod_{n\ge 1}(1-q^n)^{24},$$ the identity holding over an arbitrary commutative ring of coefficients.
--
--   This is the classical formula for the discriminant of the Tate curve, identifying it with the $q$-expansion of the weight-$12$ cusp form $\Delta$. It is used in this development to control the divisibility and unit properties of $\Delta$ along the $q$-expansion, in particular in [`ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve`](thm.html#ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve), in [`ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one`](thm.html#ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one), and in the construction of forms on $\Gamma_0$ in [`ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le`](thm.html#ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_delta_tateLaurent.lean

import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve
open PowerSeries HahnSeries in

theorem ModularCurve.delta_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).Δ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)) := by sorry
