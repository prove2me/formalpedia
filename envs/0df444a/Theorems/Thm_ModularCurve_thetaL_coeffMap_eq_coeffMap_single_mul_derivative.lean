-- Prove2me | Theorems.Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative
-- name    : ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/3c30c1ea-1e77-5efe-bbed-f3a4bfcc39c4
-- title:
--   Naturality of θ = q d/dq under coefficient base change
-- statement:
--   Let $R$ be a commutative ring, $K$ a field, $\varphi : R \to K$ a ring homomorphism, and $w$ a Laurent series over $R$ (an element of `LaurentSeries R`, i.e. a Hahn series over $R$ with value group $\mathbb{Z}$). Write `coeffMap` $\varphi$ for the ring homomorphism `LaurentSeries R →+* LaurentSeries K` obtained by applying $\varphi$ to every coefficient, and `thetaL` $K$ for the $K$-linear operator on `LaurentSeries K` sending $f$ to `HahnSeries.single 1 1` $\cdot$ `LaurentSeries.derivative K f`, that is $f \mapsto q\,f'$. The assertion is the equality of Laurent series over $K$
--   $$\mathtt{thetaL}\,K\,(\mathtt{coeffMap}\,\varphi\,w) \;=\; \mathtt{coeffMap}\,\varphi\,\bigl(\mathtt{HahnSeries.single}\,1\,1 \cdot \mathtt{LaurentSeries.derivative}\,R\,w\bigr),$$
--   so that applying $\theta = q\,d/dq$ after pushing the coefficients of $w$ along $\varphi$ gives the same result as forming $q\,w'$ over $R$ and then pushing its coefficients along $\varphi$. Note that on the right-hand side the operator is written out as multiplication by $q$ composed with the formal derivative over $R$, no operator `thetaL R` being available for a general commutative ring.
--
--   This is the naturality of the Ramanujan–Serre theta operator $\theta = q\,d/dq$ on $q$-expansions with respect to change of the coefficient ring. It is used throughout the treatment of mod $p$ modular forms, for instance when comparing $\theta$ applied to a $q$-expansion with integral coefficients to $\theta$ applied to its reduction, as in the statements about $q$-expansions of mod $p$ forms and cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean

import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative {R : Type*} [CommRing R]
    {K : Type*} [Field K] (φ : R →+* K) (w : LaurentSeries R) :
    ModularCurve.thetaL K (ModularCurve.coeffMap φ w) =
      ModularCurve.coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := by sorry
