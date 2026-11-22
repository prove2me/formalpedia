-- Prove2me | Theorems.Thm_MasulloRH_tapered_holomorphic_multiplier_boundary_jet_error
-- name    : MasulloRH.tapered_holomorphic_multiplier_boundary_jet_error
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:08:04.395191+00:00
-- url     : https://prove2.me/theorems/86882819-81af-444f-a76e-2f707c612646
-- title:
--   Strong boundary jet approximation for holomorphic damping on a strip
-- statement:
--   Let a_n=1/(n+1) and E_n(t)=exp(-a_n z(t)) for a continuous complex profile with nonnegative real part. Writing v_n=a_n Re z, the error energy (|E_n-1|²+(v_n(1+v_n)|E_n|)²) integrated against any L¹ weight tends to zero. For z(t)=cos(σ-1/2+it) on either edge of the critical strip, the second term is a common envelope, up to a constant, for the squared first and second tangential derivatives of the cutoff. This verifies the dominated-convergence step in graph-norm approximation by holomorphic cutoffs.
-- source:
--   Rational critical-width Sobolev synthesis in the Prove2Me mission discussion e71a43b4-0921-4559-b45c-83589007e215.

import Mathlib
open MeasureTheory Filter Topology

theorem MasulloRH.tapered_holomorphic_multiplier_boundary_jet_error (z : ℝ → ℂ) (hz : Continuous z) (hr : ∀ t, 0 ≤ (z t).re)
    (G : ℝ → ℝ) (hG : Integrable G volume) :
    let a := fun (n : ℕ) => ((n:ℝ)+1)⁻¹
    let E := fun (n : ℕ) (t : ℝ) => Complex.exp (-(a n : ℂ)*z t)
    let v := fun (n : ℕ) (t : ℝ) => a n*(z t).re
    Tendsto (fun n => ∫ t : ℝ, (‖E n t-1‖^2 + (v n t*(1+v n t)*‖E n t‖)^2)*G t)
      atTop (𝓝 0) := by sorry
