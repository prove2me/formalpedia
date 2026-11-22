-- Prove2me | Theorems.Thm_MasulloRH_height_one_left_compact_energy_certificate
-- name    : MasulloRH.height_one_left_compact_energy_certificate
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:52:48.233087+00:00
-- url     : https://prove2.me/theorems/25d81675-721b-4e35-ac80-05e728d7fe1a
-- title:
--   A compact theta-energy certificate on the negative half-window
-- statement:
--   Use the exact theta and Gaussian pulse in the published GaussianThetaApproximation definition. Set
--
--   $$r(x)=\frac{2}{\sqrt\pi}e^{-4x^2}-\frac{73}{50}\theta\left(x-\frac34\right),\qquad
--   F(x)=e^{\frac32x+\frac7{16}|x|}|r(x)|^2.$$
--
--   The actual density $F$ is integrable on $[-4,0]$ and satisfies
--
--   $$\int_{-4}^{0}F(x)\,dx\le\frac1{250}.$$
--
--   There are no approximation, RH, Mertens, or numerical-enclosure hypotheses. This is one compact-window component of a fixed height-one certificate, with no claim about arbitrarily large heights.
--
--   **Formalization Note.** Integrability on the stated interval is an explicit conjunct. The conclusion uses the original residual and the original theta function; finite approximations appear only in the proof.
-- source:
--   Supporting component of the explicit height-one theta-energy certificate for the actual functions at https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db . Uses the rational exponential certificate https://prove2.me/theorems/6611257a-1305-4ffc-9dd5-65de0d41a834 . The numerical candidate was selected computationally and all displayed bounds are proved in Lean. This finite-height calculation is not attributed to a page of Masullo's draft.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open MeasureTheory MasulloRH.GaussianApproximation
set_option autoImplicit false

theorem MasulloRH.height_one_left_compact_energy_certificate :
IntegrableOn (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) (Set.Icc (-4) 0) ∧
    (∫ x : ℝ in Set.Icc (-4) 0,
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) ≤ (1/250 : ℝ) := by sorry
