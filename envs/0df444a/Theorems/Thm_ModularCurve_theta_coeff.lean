-- Prove2me | Theorems.Thm_ModularCurve_theta_coeff
-- name    : ModularCurve.theta_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/ef949d2a-924c-5748-af33-47cdb6040e5a
-- title:
--   Coefficient law for θ = q d/dq on Laurent series
-- statement:
--   Let $R$ be a commutative ring and let $f$ be a formal Laurent series over $R$, that is, an element of `LaurentSeries R` $=$ `HahnSeries ℤ R`, so $f$ is given by its coefficients $f.\mathrm{coeff}\,n \in R$ indexed by $n \in \mathbb{Z}$ with well-ordered support. Let $k \in \mathbb{Z}$. Form the product of the monomial `HahnSeries.single (1 : ℤ) (1 : R)` — the series $q$, whose only nonzero coefficient is $1$ in degree $1$ — with the formal derivative `LaurentSeries.derivative R f` of $f$. The assertion is that the coefficient in degree $k$ of this product, i.e. of $\theta f = q\, f'$, equals $k \bullet (f.\mathrm{coeff}\,k)$, the action of the integer $k$ on the element $f.\mathrm{coeff}\,k$ of $R$ viewed as a $\mathbb{Z}$-module. No hypothesis beyond commutativity of $R$ is imposed; in particular $k$ ranges over all integers, positive, zero and negative, and no invertibility or characteristic assumption is made.
--
--   This is the coefficient description of the classical operator $\theta = q\,\frac{d}{dq}$ acting on $q$-expansions, here realised purely formally on Laurent series over an arbitrary commutative ring. It serves as the working interface for $\theta$ in the $q$-expansion side of the treatment of modular curves and modular forms, and is invoked by a large number of later results, among them the dimension bound [`CuspForm.dimFormula_le_finrank_gamma0`](thm.html#CuspForm.dimFormula_le_finrank_gamma0) and computations with normalised derivatives of $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_theta_coeff.lean

import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.theta_coeff {R : Type*} [CommRing R] (f : LaurentSeries R) (k : ℤ) : ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f).coeff k = k • f.coeff k := by sorry
