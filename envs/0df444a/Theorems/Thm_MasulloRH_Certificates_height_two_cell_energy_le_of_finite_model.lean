-- Prove2me | Theorems.Thm_MasulloRH_Certificates_height_two_cell_energy_le_of_finite_model
-- name    : MasulloRH.Certificates.height_two_cell_energy_le_of_finite_model
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T20:05:06.892969+00:00
-- url     : https://prove2.me/theorems/82004353-849f-477b-8c65-9f5665938404
-- title:
--   Integrated midpoint enclosure for the actual height-two theta residual
-- statement:
--   Use the eleven coefficients and shifts from `MasulloRH_HeightTwoWitness`, and let
--
--   $$r(x)=p_2(x)-\sum_{i=0}^{10}a_i\theta(x-y_i),\qquad w(x)=e^{3x/2+11|x|/24}.$$
--
--   Fix a cell $[u,v]$ with $u\le v$, a truncation length $K$, and a choice of direct or reflected finite model for each translate. A reflected choice must satisfy $v-y_i\le-1$, and a direct choice must satisfy $-1\le u-y_i$. Let $g$ be the resulting finite residual model.
--
--   Suppose $A,D,\varepsilon,W\ge0$, the finite derivative expression has absolute value at most $D$ throughout the cell, $|g((u+v)/2)|\le A$, and $w(x)\le W$ throughout the cell. Require also that its explicit truncation-error budget satisfies
--
--   $$24e^{-(K+1)^2/3}\sum_{i=0}^{10}|a_i|\left(1+\frac{e^{-(u-y_i)}}2\right)\le\varepsilon.$$
--
--   Then, writing $h=v-u$,
--
--   $$\int_u^v w(x)|r(x)|^2\,dx\le W\left[h(A+\varepsilon)^2+\frac{h^2}{2}(A+\varepsilon)D+\frac{h^3}{12}D^2\right].$$
--
--   The conclusion bounds the actual canonical residual. Integrability follows from the already proved exterior-energy theorem and is not an extra premise. The finite derivative expression is proved to be the derivative of $g$ inside the proof.
-- source:
--   Reusable soundness theorem constructed for the independent theta-approximation branch of the Prove2Me Masullo RH specialization mission. It supports the exact eleven-term height-two certificate and uses the published MasulloRH_ThetaCertificate definitions. This is a new supporting construction, not a theorem attributed to a particular manuscript passage.

import Mathlib
import Definitions.Def_MasulloRH_ThetaCertificate
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory Set _root_.MasulloRH _root_.MasulloRH.GaussianApproximation
open _root_.MasulloRH.Certificates _root_.MasulloRH.CertifiedExp

theorem MasulloRH.Certificates.height_two_cell_energy_le_of_finite_model
    (K : ℕ) (branch : Fin 11 → Bool)
    {u v A D epsilon W : ℝ}
    (huv : u ≤ v) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hepsilon : 0 ≤ epsilon) (hW : 0 ≤ W)
    (hbranch : ∀ i, if branch i then v - HeightTwoWitness.shifts i ≤ -1
      else -1 ≤ u - HeightTwoWitness.shifts i)
    (hderiv : ∀ x ∈ Icc u v,
      |finiteResidualDerivative K 2 (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
        HeightTwoWitness.shifts branch x| ≤ D)
    (hmid :
      |finiteResidualModel K 2 (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
        HeightTwoWitness.shifts branch ((u + v) / 2)| ≤ A)
    (herror : finiteResidualErrorBudget K (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
      HeightTwoWitness.shifts u ≤ epsilon)
    (hweight : ∀ x ∈ Icc u v,
      Real.exp (2*(3/4)*x+2*(11/48)*|x|) ≤ W) :
    (∫ x : ℝ in Icc u v, Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2) ≤
      W*((v-u)*(A+epsilon)^2 +
        (v-u)^2*(A+epsilon)*D/2 + (v-u)^3*D^2/12) := by sorry
