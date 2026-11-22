-- Prove2me | Theorems.Thm_MasulloRH_height_one_left_inner_compact_energy_certificate
-- name    : MasulloRH.height_one_left_inner_compact_energy_certificate
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:44:15.097174+00:00
-- url     : https://prove2.me/theorems/580f5afe-c496-4120-99d1-f46259bc3ba6
-- title:
--   Theta energy on [-1/4,0]
-- statement:
--   For the exact canonical theta function and Gaussian pulse, set
--
--   $$r(x)=\frac{2}{\sqrt\pi}e^{-4x^2}-\frac{73}{50}\theta\left(x-\frac34\right),\qquad
--   F(x)=e^{\frac32x+\frac7{16}|x|}|r(x)|^2.$$
--
--   The density $F$ is integrable on $[\frac{-1}{4},0]$ and
--
--   $$\int_{\frac{-1}{4}}^{0}F(x)\,dx\le \frac{7}{8000}.$$
--
--   This is an unconditional compact-interval statement at height parameter one. Integrability on the stated interval is an explicit conjunct. The conclusion uses the original canonical residual and theta function and makes no claim about a cofinal family of heights.
-- source:
--   Supporting compact-interval component for the exact functions in https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db . Uses the accepted analytic theta estimates https://prove2.me/theorems/8632ce84-3f47-4ac8-b2ff-ae87b3a5a9fe , https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 , and https://prove2.me/theorems/25b37d57-49aa-48a9-a889-c77a60c8d626 .

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open MeasureTheory MasulloRH.GaussianApproximation
set_option autoImplicit false

theorem MasulloRH.height_one_left_inner_compact_energy_certificate :
    IntegrableOn (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) (Set.Icc (-1 / 4 : ℝ) (0 : ℝ)) ∧
    (∫ x : ℝ in Set.Icc (-1 / 4 : ℝ) (0 : ℝ),
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) ≤ (7 / 8000 : ℝ) := by sorry
