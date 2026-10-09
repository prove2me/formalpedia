-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_ball_average_eq_of_sphereAverage_eq
-- name    : HunterPDE.Harmonic.ball_average_eq_of_sphereAverage_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T18:55:36.42334+00:00
-- url     : https://prove2.me/theorems/79c1d2d7-4128-4151-8f7a-66c147c4346d
-- title:
--   Constant spherical averages give the same ball average
-- statement:
--   Let $n\ge1$, $r>0$, and let $u$ be continuous on $\overline B_r(x)\subset\mathbb R^n$. Suppose that its normalized surface average equals a fixed real number $c$ at every radius $0<t\le r$. Then
--
--   $$\frac{1}{|B_r(x)|}\int_{B_r(x)}u(y)\,dy=c.$$
--
--   This is the polar-coordinate averaging step in Hunter's proof of Theorem 2.1, obtained from Proposition 1.45. It does not assume harmonicity and can be reused for any continuous function with constant spherical means.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 20, proof of Theorem 2.1, Eq. (2.4); polar integration: p. 17, Proposition 1.45.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

open MeasureTheory Set
open HunterPDE.Harmonic

namespace HunterPDE.Harmonic

theorem ball_average_eq_of_sphereAverage_eq {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r c : ℝ} (hr : 0 < r)
    (hu : ContinuousOn u (Metric.closedBall x r))
    (havg : ∀ t ∈ Ioc 0 r, sphereAverage u x t = c) :
    (⨍ y in Metric.ball x r, u y) = c := by sorry

end HunterPDE.Harmonic
