-- Prove2me | Theorems.Thm_MilnorDynamics_cayley_I_disk_lt_upper_halfplane
-- name    : MilnorDynamics.cayley_I_disk_lt_upper_halfplane
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T14:43:53.971487+00:00
-- url     : https://prove2.me/theorems/43792ee7-7ad7-4c72-8da4-d9eb1d6a8d3a
-- title:
--   The twisted Cayley transform sends the open unit disc into the upper half-plane
-- statement:
--   For every point $z$ of the open unit disc in $\mathbb{C}$, the twisted Cayley transform $w = I\,(z+1)/(1-z)$ has strictly positive imaginary part, i.e. $0 < \operatorname{Im} w$. Equivalently the map $z \mapsto I(z+1)/(1-z)$ carries the open unit disc into the upper half-plane $\{w : \operatorname{Im} w > 0\}$. The untwisted Cayley transform $(z+1)/(1-z)$ lands in the RIGHT half-plane, which is already proved; the extra factor $I$ rotates that half-plane onto the upper one, and the rotation converts the real-part inequality into an imaginary-part one.
-- source:
--   Milnor, Dynamics in One Complex Variable I, Lemma 2.5 (the thrice-punctured sphere is hyperbolic); the standard biholomorphism from the open unit disc to the upper half-plane is the Cayley transform with the prefactor $I$.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open Complex

namespace MilnorDynamics

/-- The Cayley transform `c z = (z + 1) / (1 - z)` sends the open unit disc onto the
RIGHT half-plane; the sibling `cayley_disk_lt_halfplane` (`a5dd6f7c`) has already proved
the real part of that fact.  Milnor's uniformisation route needs the UPPER half-plane,
which is obtained by the single extra prefactor `I`: the map `w z = I * (z + 1) / (1 - z)`
carries the disc onto `{w : C | 0 < w.im}`.

This is the landing half of the corrected `cayley_biholo_disc_halfplane` (`0b98590f`),
which was `Disproved` only because its first conjunct quantified over `Set.univ` rather
than over the disc.  The fact is a corollary of the Proved real-part statement together
with `Complex.I_mul_im (z : C) : (I * z).im = z.re`
(`Mathlib/Data/Complex/Basic.lean:273`), so it carries no analytic content of its own.

It is a prerequisite for composing the modular lambda function with the disc, and it is
the reason the `exp`-based witnesses fail: `exp` of the RIGHT half-plane is
`C \ (-inf, 0]`, which misses the negative real axis entirely. -/
theorem cayley_I_disk_lt_upper_halfplane (z : ℂ) (hz : z ∈ Metric.ball 0 1) :
    0 < (I * ((z + 1) / (1 - z))).im := by sorry

end MilnorDynamics
