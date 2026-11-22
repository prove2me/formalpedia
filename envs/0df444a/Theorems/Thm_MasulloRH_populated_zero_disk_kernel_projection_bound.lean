-- Prove2me | Theorems.Thm_MasulloRH_populated_zero_disk_kernel_projection_bound
-- name    : MasulloRH.populated_zero_disk_kernel_projection_bound
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:40:09.164196+00:00
-- url     : https://prove2.me/theorems/3e068c6a-7f59-4c81-b6a8-04f164bd4904
-- title:
--   Populated zero disks exponentially suppress the orthogonal projection of an interior Mellin evaluation kernel
-- statement:
--   In a Hilbert space of disk-chart transforms, suppose the center evaluation is represented by k. If every normalized vector in the projected subspace has a uniform boundary bound M on radius R and at least N inner zeros counted with multiplicity in radius r whenever the center value is nonzero, then the orthogonal projection of k has norm at most M exp(−N log(R/r)). This gives a quantitative projection estimate for populated zero bins in a compact interior chart.
-- source:
--   Masullo mission discussion of translated zero bins (8885a540-7086-4189-be39-e9b94908a999); Stefan Kebekus, Jensen inequality in Mathlib.Analysis.Complex.JensenFormula.

import Mathlib
open Metric MeromorphicOn
open scoped InnerProductSpace

theorem MasulloRH.populated_zero_disk_kernel_projection_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (F : H → ℂ → ℂ) (c : ℂ) (k : H)
    (eval : ∀ g, F g c = ⟪k, g⟫_ℂ)
    (r R M : ℝ) (N : ℕ) (hr : 0 < r) (hR : r < R) (hM : 1 ≤ M)
    (analytic : ∀ g ∈ U, ‖g‖ = 1 → AnalyticOnNhd ℂ (F g) (closedBall c R))
    (bound : ∀ g ∈ U, ‖g‖ = 1 → ∀ z ∈ sphere c R, ‖F g z‖ ≤ M)
    (zeros : ∀ g ∈ U, ‖g‖ = 1 → F g c ≠ 0 →
      (N : ℤ) ≤ ∑ᶠ z, divisor (F g) (closedBall c r) z) :
    ‖U.starProjection k‖ ≤ M * Real.exp (-(N : ℝ) * Real.log (R / r)) := by sorry
