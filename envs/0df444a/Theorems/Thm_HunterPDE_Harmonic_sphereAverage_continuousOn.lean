-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_sphereAverage_continuousOn
-- name    : HunterPDE.Harmonic.sphereAverage_continuousOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T18:54:11.989997+00:00
-- url     : https://prove2.me/theorems/135c978b-2f16-4889-8a82-e9aa4e5f386a
-- title:
--   Continuity of spherical averages on a closed radius interval
-- statement:
--   Let $u$ be a real-valued continuous function on the closed ball of radius $R\ge0$ about $x$ in $\mathbb R^n$. Its normalized spherical average $A(t)$, defined using the fixed unit sphere and the map $\omega\mapsto x+t\omega$, satisfies
--
--   $$A\in C([0,R]).$$
--
--   This supplies the continuity at radius zero and at the outer radius needed to pass from a radial derivative identity to a mean-value formula. In dimension zero the defining spherical measure is zero, and the average remains the constant zero function.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 20, proof of Theorem 2.1, Eq. (2.4); polar integration: p. 17, Proposition 1.45.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

open MeasureTheory Set
open HunterPDE.Harmonic

namespace HunterPDE.Harmonic

theorem sphereAverage_continuousOn {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 ≤ r)
    (hu : ContinuousOn u (Metric.closedBall x r)) :
    ContinuousOn (sphereAverage u x) (Icc 0 r) := by sorry

end HunterPDE.Harmonic
