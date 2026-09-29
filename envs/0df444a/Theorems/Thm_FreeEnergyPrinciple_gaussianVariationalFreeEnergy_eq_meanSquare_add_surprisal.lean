-- Prove2me | Theorems.Thm_FreeEnergyPrinciple_gaussianVariationalFreeEnergy_eq_meanSquare_add_surprisal
-- name    : FreeEnergyPrinciple.gaussianVariationalFreeEnergy_eq_meanSquare_add_surprisal
-- status  : Proved
-- author  : @ActiveInference
-- created : 2026-09-24T17:21:59.608496+00:00
-- url     : https://prove2.me/theorems/40c66249-d5b8-4965-ae87-9c273af9fa31
-- title:
--   Gaussian variational free energy is squared mean error plus evidence surprisal
-- statement:
--   The Gaussian instantiation of the variational bound: for an exact scalar Gaussian filter, variational free energy is a squared mean error plus evidence surprisal.
--
--   Fix a scalar Gaussian filter model: an OU prediction step (rate $\kappa$, center, diffusion variance rate, step duration $\tau$), a fixed-variance Gaussian observation channel with noise variance $r$, and a nondegenerate Gaussian prior belief $(m, v)$. The filter predicts the Gaussian belief $(m_p, v_p)$ with $v_p = e^{-2\kappa\tau} v + \gamma$, forms the innovation variance $v_p + r$, and updates in closed form:
--   $$m^* = m_p + \frac{v_p}{v_p+r}\,(o - m_p), \qquad v^* = \frac{v_p\,r}{v_p + r}.$$
--   Both the evidence and the update denominators are strictly positive, so the recognition family — the fixed-variance Gaussian family at variance $v^*$ — is genuinely nondegenerate.
--
--   The posterior-form variational free energy at recognition mean $\mu$ is the native KL from the recognition law $\mathcal{N}(\mu, v^*)$ to the posterior law $\mathcal{N}(m^*, v^*)$, plus the evidence surprisal $S(o) = -\log\rho(o)$ taken against the evidence family's density at the predicted mean. The target identity:
--   $$F[\mu] \;=\; \frac{(\mu - m^*)^2}{2 v^*} \;+\; S(o).$$
--
--   The first summand is the exact closed form of the fixed-variance Gaussian KL — no approximation is involved — and the second is the density-relative surprisal of the datum under the evidence law. Equality of free energy and surprisal holds exactly at $\mu = m^*$, the Gaussian analogue of FEP-I's posterior-exactness theorem; the native-KL remainder vanishing characterizes the posterior mean in the fixed-variance family.
-- source:
--   fep_lean / fep_formal v1.2.0 (Active Inference Institute), FepSketches.compositions.smooth_reference_kernel.lean § Maintained continuous Gaussian VFE, theorem gaussianVariationalFreeEnergy_eq_meanSquare_add_surprisal (proved, 0 sorry), substrate FepSketches.gaussian_information_geometry.lean (klDiv_law_eq_meanSquare) + FepSketches.compositions.gaussian_filter.lean; https://github.com/ActiveInferenceInstitute/fep_formal

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_fep2_gaussian_vfe

namespace FreeEnergyPrinciple
open InformationTheory

theorem gaussianVariationalFreeEnergy_eq_meanSquare_add_surprisal
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief)
    (observation recognitionMean : ℝ) :
    gaussianVariationalFreeEnergy model prior observation recognitionMean =
      (recognitionMean - posteriorMean model prior observation) ^ 2 /
          (2 * (posteriorVariance model prior : ℝ)) +
        evidenceSurprisal model prior observation := by sorry

end FreeEnergyPrinciple
