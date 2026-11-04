-- Prove2me | Theorems.Thm_Grothendieck_integral_sqrt_inv_mul_eq
-- name    : Grothendieck.integral_sqrt_inv_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:24:07.118395+00:00
-- url     : https://prove2.me/theorems/576ff743-b04b-48d0-be78-2166b5c24f87
-- title:
--   The density form of $s=u^2/2$: $(2s)^{-1/2}ds$ is the pushforward under $u\mapsto u^2/2$
-- statement:
--   For a measurable $f$ on the positive half-line,
--   $$\int_0^\infty \frac{f(s)}{\sqrt{2s}}\,ds=\int_0^\infty f\!\left(\frac{u^2}{2}\right)du .$$
--   Equivalently, the measure with density $(2s)^{-1/2}$ on $(0,\infty)$ is the pushforward of Lebesgue measure under $u\mapsto u^2/2$, whose derivative is $u$ and whose image of $(0,\infty)$ is itself.
--
--   This is the one-dimensional ingredient of the substitution $s=u^2/2$ in the Laplace parameters of Lemma 2.1: the singular factor $(st)^{-1/2}$ that the two-parameter integral carries is exactly $2\cdot(2s)^{-1/2}(2t)^{-1/2}$, so applying this identity in each variable converts the $(s,t)$ integral into a $(u,v)$ integral with no singular factor at all.
--
--   **Formalization Note** Proved by the image formula for the Lebesgue integral with $u\mapsto u^2/2$; no integrability hypothesis is needed, the identity being an equality of Bochner integrals (both sides are `0` when the other is).
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - the substitution s=p^2/2 in the proof of Lemma 2.1.

import Mathlib

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The density form of `s = u²/2`.** For a measurable `f`,
`∫₀^∞ f(s)·(√(2s))⁻¹ ds = ∫₀^∞ f(u²/2) du`: the measure `(√(2s))⁻¹ds` on the positive half-line is
the pushforward of Lebesgue measure under `u ↦ u²/2`. -/
theorem integral_sqrt_inv_mul_eq {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ s in Set.Ioi (0:ℝ), (Real.sqrt (2 * s))⁻¹ * f s)
      = ∫ u in Set.Ioi (0:ℝ), f (u ^ 2 / 2) := by sorry

end Grothendieck
