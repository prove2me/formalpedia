-- Prove2me | Theorems.Thm_MasulloRH_height_two_theta_energy_certificate
-- name    : MasulloRH.height_two_theta_energy_certificate
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T09:20:52.748002+00:00
-- url     : https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e
-- title:
--   The eleven-term rational theta witness has height-two energy below one ninety-sixth
-- statement:
--   Use the exact rational eleven-term witness from \( \mathrm{MasulloRH.HeightTwoWitness}\) with the canonical pulse and theta. Its weighted squared residual is integrable on the real line and satisfies
--
--   \[
--    \int_{\mathbb R}e^{3x/2+11|x|/24}
--      \left|\operatorname{pulse}(2,x)-\sum_{i=1}^{11}a_i\theta(x-y_i)\right|^2\,dx
--    < \frac1{96}.
--   \]
--
--   This is the strict Gram margin at the single scale \(n=2\), where \(\delta=1/48\). It gives a concrete test case for the cofinal exact-margin problem.
-- source:
--   Scale-two specialization of MasulloRH.cofinal_exact_theta_gram_margin, https://prove2.me/theorems/b2ce922d-3f53-4192-b8a7-484fcd931614 . The explicit witness and exterior result are from the earlier finite-height mission work, https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d and https://prove2.me/theorems/64eea16b-a1b5-4d72-9c75-6b61b57ddea4 .

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness

open MeasureTheory MasulloRH MasulloRH.GaussianApproximation
set_option autoImplicit false

theorem MasulloRH.height_two_theta_energy_certificate :
    Integrable (fun x : ℝ => Real.exp (2*(3/4)*x + 2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2) ∧
    energy (3/4) (11/48) (residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts) < 1/96 := by sorry
