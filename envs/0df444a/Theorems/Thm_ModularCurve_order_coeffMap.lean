-- Prove2me | Theorems.Thm_ModularCurve_order_coeffMap
-- name    : ModularCurve.order_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/1227cb5c-ba83-5b01-b8d1-9a73ca7663e7
-- title:
--   Coefficientwise injections preserve the order of a Laurent series
-- statement:
--   Let $R$ and $S$ be commutative rings and let $\varphi : R \to S$ be a ring homomorphism which is injective as a function. Let $x$ be a Laurent series over $R$, i.e. an element of `LaurentSeries R`, the Hahn series over $R$ with value group $\mathbb{Z}$. Write `coeffMap φ` for the ring homomorphism `LaurentSeries R →+* LaurentSeries S` whose underlying function sends a series to its coefficientwise image under $\varphi$ (the Hahn series `map` applied to $\varphi$), the ring-homomorphism structure being the evident compatibility of coefficientwise application with $0$, $1$, addition and multiplication. The assertion is the equality of orders
--   $$\operatorname{order}(\mathrm{coeffMap}\ \varphi\ x) = \operatorname{order}(x)$$
--   in $\mathbb{Z}$, where $\operatorname{order}$ is the Mathlib order of a Hahn series: the least index with nonvanishing coefficient when the series is nonzero, and $0$ by convention for the zero series. Thus for $x \neq 0$ the two sides are the genuine orders of $x$ and of its coefficientwise image, and for $x = 0$ both sides are $0$.
--
--   This is the statement that an injective coefficient map on Laurent series is order-preserving; it is the basic compatibility needed when a Laurent-series expansion is transported along an injection of coefficient rings, for instance along a scalar extension. It is used in the analysis of places of a curve after base change to a Laurent series field ([`AlgebraicCurve.Place.exists_place_laurentBaseChange_of_deg_eq_one`](thm.html#AlgebraicCurve.Place.exists_place_laurentBaseChange_of_deg_eq_one)) and in the criterion [`ModularCurve.arithmeticGalois_smul_mem_qIntegersBar_iff`](thm.html#ModularCurve.arithmeticGalois_smul_mem_qIntegersBar_iff) for membership in the ring of $q$-integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_order_coeffMap.lean

import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.order_coeffMap {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S} (hφ : Function.Injective φ) (x : LaurentSeries R) : (coeffMap φ x).order = x.order := by sorry
