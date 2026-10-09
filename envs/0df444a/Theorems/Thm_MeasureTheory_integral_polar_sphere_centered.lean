-- Prove2me | Theorems.Thm_MeasureTheory_integral_polar_sphere_centered
-- name    : MeasureTheory.integral_polar_sphere_centered
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T10:21:38.440246+00:00
-- url     : https://prove2.me/theorems/43c0c0ea-9b7f-4142-bc02-6041daadbc3a
-- title:
--   Centered polar integration against Haar-induced sphere measure
-- statement:
--   Let $n\ge1$, $x\in\mathbb R^n$, and let $f:\mathbb R^n\to\mathbb R$ be Lebesgue integrable. Let $\sigma$ be the Haar-induced surface measure on the unit sphere. Then
--
--   $$\int_{\mathbb R^n}f(y)\,dy=\int_0^\infty\left(\int_{S^{n-1}}f(x+t\omega)\,d\sigma(\omega)\right)t^{n-1}\,dt.$$
--
--   This centered polar-coordinate formula is useful for radial integration and separating boundary flux calculations from their radial weights.
--
--   **Formalization Note** The radial density is represented by Mathlib's measure on the positive-ray subtype.
-- source:
--   Hunter, Notes on PDEs, printed p. 17, Proposition 1.45, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf; Mathlib MeasureTheory/Constructions/HaarToSphere.lean, measurePreserving_homeomorphUnitSphereProd.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory MeasureTheory.Measure Set Metric Filter Function
open scoped Topology
set_option autoImplicit false

theorem MeasureTheory.integral_polar_sphere_centered {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f) :
    (∫ y, f y) = ∫ t : Ioi (0 : ℝ),
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        f (x + t.1 • ω.1) ∂volume.toSphere ∂Measure.volumeIoiPow (n - 1) := by sorry
