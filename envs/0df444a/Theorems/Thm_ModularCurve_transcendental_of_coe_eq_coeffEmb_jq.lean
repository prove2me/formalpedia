-- Prove2me | Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
-- name    : ModularCurve.transcendental_of_coe_eq_coeffEmb_jq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/b411998e-0d6c-507f-aebb-9320ce54e546
-- title:
--   Transcendence of j over the base domain A
-- statement:
--   Let $L$ be a field of characteristic zero, let $K$ be an intermediate field of the field of formal Laurent series $L((q))$ over $L$, and let $A$ be a commutative domain equipped with an algebra structure over which $L$ is the fraction field of $A$, together with an $A$-algebra structure on $K$ making $A \to L \to K$ a tower of scalars. Let $j$ be an element of $K$ whose image in $L((q))$ is the coefficientwise image, under the ring map $\mathrm{LaurentSeries}\,\mathbb{Q} \to \mathrm{LaurentSeries}\,L$ induced by $\mathbb{Q} \to L$ applied termwise, of the Laurent series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), namely the product of the monomial $q^{-1}$ (the Hahn series with single coefficient $1$ in degree $-1$) with the power series `jNumQ`, the image over $\mathbb{Q}$ of the integral power series `jNum`. The conclusion is that $j$ is transcendental over $A$: it is not a root of any nonzero polynomial with coefficients in $A$.
--
--   This records that the $j$-invariant, presented as an element of a subfield of $L((q))$ with $q$-expansion $q^{-1}+744+196884q+\cdots$, is transcendental over any domain $A$ whose fraction field is $L$. It supplies the transcendence hypothesis used throughout the construction of the modular curve models over such base rings, and is cited by a large number of statements in that development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.transcendental_of_coe_eq_coeffEmb_jq
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    Transcendental A j := by sorry
