-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_zero
-- name    : HunterPDE.Harmonic.hasDerivAt_sphereAverage_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T18:54:37.240132+00:00
-- url     : https://prove2.me/theorems/dcdb1268-cfdd-4c78-b348-10d8e2dee6e0
-- title:
--   Vanishing radial derivative of spherical averages of harmonic functions
-- statement:
--   Let $n\ge1$, $r>0$, and let $u$ be harmonic in a neighborhood of every point of the closed ball $\overline B_r(x)\subset\mathbb R^n$. Write $A(t)$ for the normalized surface average of $u$ on the sphere of radius $t$ about $x$. Then
--
--   $$A'(r)=0.$$
--
--   This is the harmonic specialization of Hunter's radial derivative identity (2.4). It isolates the differentiation-under-the-integral and divergence-theorem step, and applies without selecting a surrounding open domain.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 20, proof of Theorem 2.1, Eq. (2.4); polar integration: p. 17, Proposition 1.45.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

open MeasureTheory Set
open HunterPDE.Harmonic

namespace HunterPDE.Harmonic

theorem hasDerivAt_sphereAverage_zero {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall x r)) :
    HasDerivAt (sphereAverage u x) 0 r := by sorry

end HunterPDE.Harmonic
