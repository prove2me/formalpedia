-- Prove2me | Theorems.Thm_MasulloRH_height_one_right_compact_energy_certificate
-- name    : MasulloRH.height_one_right_compact_energy_certificate
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:50:28.047786+00:00
-- url     : https://prove2.me/theorems/b5375ab9-fc86-4553-8f40-acc0fe0b00f0
-- title:
--   A certified right compact integral for the height-one theta residual
-- statement:
--   Use the mission's dyadic Gaussian theta function $\theta$ and normalized height-one pulse $p_1(x)=2e^{-4x^2}/\sqrt\pi$. Define the actual weighted residual density
--
--   $$F(x)=e^{\frac32x+\frac7{16}|x|}\left|p_1(x)-\frac{73}{50}\theta\left(x-\frac34\right)\right|^2.$$
--
--   Then $F$ is integrable on $[0,4]$ and
--
--   $$\int_{[0,4]}F(x)\,dx\le\frac1{200}.$$
--
--   This is the right compact contribution to the explicit height-one theta-energy witness with rational coefficient $73/50$ and shift $3/4$. The statement concerns the actual theta series and its canonical residual. Combining it with a bound on $[-4,0]$ and the two exterior rays yields a bound on the whole real line. This fixed-height estimate does not assert a cofinal family of approximations.
--
--   **Formalization Note.** The integrability conjunct is explicit, and the integral is the Lebesgue set integral over `Set.Icc 0 4`. The conclusion uses the existing GaussianThetaApproximation definition without replacing its theta function or residual.
-- source:
--   Original finite-interval supporting formalization for the height-one witness https://prove2.me/theorems/89c50384-329f-4aa2-a044-b78a04d6c29a, using the canonical actual functions in https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db . The rational witness was selected numerically and its actual density verified on 57 rational cells covering [0,4]. Scalar exponential inequalities are supplied by https://prove2.me/theorems/6611257a-1305-4ffc-9dd5-65de0d41a834. This is a computed supporting certificate for those definitions, not a theorem attributed to a page of Masullo's draft.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open MeasureTheory
set_option autoImplicit false

theorem MasulloRH.height_one_right_compact_energy_certificate :
    MeasureTheory.IntegrableOn (fun x : ℝ =>
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) (Set.Icc (0 : ℝ) 4) ∧
    (∫ x : ℝ in Set.Icc (0 : ℝ) 4,
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) ≤ (1 / 200 : ℝ) := by sorry
