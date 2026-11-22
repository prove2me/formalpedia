-- Prove2me | Theorems.Thm_MasulloRH_height_two_residual_exterior_bound
-- name    : MasulloRH.height_two_residual_exterior_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T19:23:54.560327+00:00
-- url     : https://prove2.me/theorems/64eea16b-a1b5-4d72-9c75-6b61b57ddea4
-- title:
--   Integrability and exterior energy of the eleven-term height-two theta witness
-- statement:
--   Let $a_i,y_i$ be the eleven exact rational coefficients and shifts in `MasulloRH_HeightTwoWitness`, indexed by $0\le i<11$. Use the canonical Gaussian pulse and actual theta function to define
--
--   $$r(x)=\frac3{\sqrt\pi}e^{-9x^2}-\sum_{i=0}^{10}a_i\theta(x-y_i),\qquad w(x)=e^{3x/2+11|x|/24}.$$
--
--   Then $x\mapsto w(x)|r(x)|^2$ is Lebesgue integrable, and its full and truncated energies obey
--
--   $$0\le\int_{\mathbb R}w(x)|r(x)|^2\,dx-\int_{-4}^{4}w(x)|r(x)|^2\,dx\le10^{-10}.$$
--
--   Thus the discarded tails contribute at most the displayed rational allowance to this fixed witness's energy. The finite-window energy is a separate quantity and is not bounded by this theorem.
--
--   **Formalization Note.** The coefficients are canonically embedded in $\mathbb C$ and the shifts in $\mathbb R$. The finite-window integral uses `Set.Icc (-4) 4`. Integrability and nonnegative discarded energy are both conclusions; the theorem has no assumptions.
-- source:
--   Supporting explicit certificate for the Masullo RH specialization mission. Uses the canonical GaussianThetaApproximation definition, the exact HeightTwoWitness data, and the proved general finite-residual tail theorem https://prove2.me/theorems/2d121368-d18c-484d-9ad7-8213e62d8b2d . This fixed-witness estimate was constructed for this contribution; no claim of an estimate from a particular manuscript page is made.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness
open MeasureTheory Set
set_option autoImplicit false

theorem MasulloRH.height_two_residual_exterior_bound :
    Integrable (fun x : ℝ =>
      Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
        ‖_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts x‖^2) ∧
    0 ≤ _root_.MasulloRH.GaussianApproximation.energy (3/4) (11/48) (_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts) -
      (∫ x : ℝ in Icc (-4) 4,
        Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
          ‖_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts x‖^2) ∧
    _root_.MasulloRH.GaussianApproximation.energy (3/4) (11/48) (_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts) -
      (∫ x : ℝ in Icc (-4) 4,
        Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
          ‖_root_.MasulloRH.GaussianApproximation.residual 2 _root_.MasulloRH.HeightTwoWitness.coeffs _root_.MasulloRH.HeightTwoWitness.shifts x‖^2) ≤
      (1/10000000000 : ℝ) := by sorry
