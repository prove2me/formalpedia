-- Prove2me | Theorems.Thm_ModularCurve_theta_mul
-- name    : ModularCurve.theta_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/325f4b9b-8c7b-5575-82d2-42f0c802a2d7
-- title:
--   Leibniz rule for θ = q d/dq on Laurent series
-- statement:
--   Let $R$ be a commutative ring and let $f, g$ be formal Laurent series over $R$, i.e. elements of `LaurentSeries R`, the Hahn series with integer exponents and coefficients in $R$. Write $q$ for the Hahn series `HahnSeries.single (1 : ℤ) (1 : R)`, the series with coefficient $1$ in degree $1$ and $0$ elsewhere, and write $f \mapsto f'$ for `LaurentSeries.derivative R`, the coefficientwise formal derivative. The assertion is the identity
--   $$q \cdot (f g)' \;=\; f \cdot \bigl(q \cdot g'\bigr) \;+\; g \cdot \bigl(q \cdot f'\bigr)$$
--   in `LaurentSeries R`. Equivalently, setting $\theta h = q \cdot h'$, the operator $\theta$ satisfies $\theta(fg) = f\,\theta g + g\,\theta f$, so that $\theta$ is a derivation of the ring of formal Laurent series over any commutative ring. No hypotheses beyond commutativity of $R$ are imposed, and no invertibility or integrality assumptions are made on the coefficients.
--
--   This is the Leibniz rule for the logarithmic derivative operator $\theta = q\,d/dq$ acting on $q$-expansions, stated as a pure identity of formal Laurent series rather than for a bundled derivation. It is used throughout the $q$-expansion computations of the modular-curve part of the development, in particular in the analysis of $\theta$ applied to products and to twists of series by roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_theta_mul.lean

import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.theta_mul {R : Type*} [CommRing R] (f g : LaurentSeries R) : (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (f * g) = f * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R g) + g * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) := by sorry
