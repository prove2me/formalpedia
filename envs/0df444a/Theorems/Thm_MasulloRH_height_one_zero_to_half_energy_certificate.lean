-- Prove2me | Theorems.Thm_MasulloRH_height_one_zero_to_half_energy_certificate
-- name    : MasulloRH.height_one_zero_to_half_energy_certificate
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:44:15.607657+00:00
-- url     : https://prove2.me/theorems/76ba3b55-6459-4c63-9576-fdebf6b9b0c3
-- title:
--   Height-one theta residual energy on the interval [0, 1/2]
-- statement:
--   Let $\theta$ be the mission's actual dyadic Gaussian theta function and let $p_1(x)=2e^{-4x^2}/\sqrt\pi$. Put
--
--   $$F(x)=e^{\frac32x+\frac7{16}|x|}\left|p_1(x)-\frac{73}{50}\theta\left(x-\frac34\right)\right|^2.$$
--
--   Then $F$ is integrable on $[0,1/2]$ and
--
--   $$\int_{[0,1/2]}F(x)\,dx\le\frac{11}{5000}.$$
--
--   This estimate is a compact subinterval contribution to the explicit height-one witness with coefficient $73/50$ and shift $3/4$. The complementary interval estimate combines with it to bound the integral over $[0,4]$ by $1/200$. The statement concerns the actual theta series and its canonical residual, and makes no cofinal approximation or RH assertion.
--
--   **Formalization Note.** Integrability on the stated closed interval is an explicit conjunct. The integral is the Lebesgue set integral of the existing GaussianThetaApproximation residual; no replacement theta function, numerical oracle, or table-validity hypothesis appears.
-- source:
--   Original finite-subinterval supporting formalization for the actual height-one witness https://prove2.me/theorems/89c50384-329f-4aa2-a044-b78a04d6c29a . Uses the canonical functions from https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db and accepted reflection/Gaussian truncation/reflected-evaluation error theorems. The rational interval certificate is a supporting computation for those definitions, not a result attributed to a page of Masullo's draft.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open MeasureTheory
set_option autoImplicit false

theorem MasulloRH.height_one_zero_to_half_energy_certificate :
    MeasureTheory.IntegrableOn (fun x : ℝ =>
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) ∧
    (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 2 : ℝ),
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) ≤ (11 / 5000 : ℝ) := by sorry
