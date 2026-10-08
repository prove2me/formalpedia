-- Prove2me | Theorems.Thm_MethanolMuDrift_eLine_two_sigma_level
-- name    : MethanolMuDrift.eLine_two_sigma_level
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T22:25:35.464195+00:00
-- url     : https://prove2.me/theorems/c80c00e4-9faf-4b12-8688-86380ad00766
-- title:
--   E-line result is consistent with no variation at the $1.5\times10^{-7}$ level
-- statement:
--   For the weighted least-squares fit of the three E lines (see the E-line fit milestone), with estimate $\widehat{\Delta\mu/\mu}=-b/c$ and statistical error $\sigma=\sigma_b/c$, the estimate lies within two standard errors of zero and the two-standard-error bound equals $1.5\times10^{-7}$ to the stated precision:
--   $$\big|\widehat{\Delta\mu/\mu}\big|\le2\sigma,\qquad |2\sigma-1.5\times10^{-7}|\le0.05\times10^{-7}.$$
--   This is the paper's statement that the E-line result "is consistent with a non-varying $\mu$ at the level of $1.5\times10^{-7}$ (95% confidence level)".
--
--   **Formalization Note** The "95% confidence level" is rendered as the two-standard-error interval $\pm2\sigma$ (the usual Gaussian approximation); this reading is an interpretation, since the paper does not spell out the multiplier.
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, p. 2 (left column): "... which is consistent with a non-varying μ at the level of 1.5×10^-7 (95% confidence level)."

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift

theorem eLine_two_sigma_level :
    |muDriftEstimate eK eV eSigma| ≤ 2 * muDriftStatErr eK eSigma ∧
      |2 * muDriftStatErr eK eSigma - 1.5e-7| ≤ 0.05e-7 := by sorry

end MethanolMuDrift
