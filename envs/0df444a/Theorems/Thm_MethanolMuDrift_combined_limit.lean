-- Prove2me | Theorems.Thm_MethanolMuDrift_combined_limit
-- name    : MethanolMuDrift.combined_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T01:40:33.949051+00:00
-- url     : https://prove2.me/theorems/5c849c92-ef5c-4b5a-9e25-e2d3b8351754
-- title:
--   Main result: $\Delta\mu/\mu=(0.0\pm1.0)\times10^{-7}$ at $z=0.89$
-- statement:
--   Let $\widehat{\Delta\mu/\mu}=-b/c$ and $\sigma_{\mathrm{stat}}=\sigma_b/c$ be the estimate and statistical error obtained from the weighted least-squares fit of the three E-symmetry methanol lines of Table 1 (positions plotted against sensitivity coefficients $K_\mu$), and let $\sigma_{\mathrm{sys}}=7.0\times10^{-8}$ be the systematic uncertainty adopted for source variability. Adding the two uncertainties in quadrature, the result rounds to the paper's headline limit $\Delta\mu/\mu=(0.0\pm1.0)\times10^{-7}$:
--   $$\big|\widehat{\Delta\mu/\mu}\big|<0.05\times10^{-7},\qquad\Big|\sqrt{\sigma_{\mathrm{stat}}^2+\sigma_{\mathrm{sys}}^2}-1.0\times10^{-7}\Big|<0.05\times10^{-7}.$$
--   This is the constraint on a cosmological variation of the proton-to-electron mass ratio at redshift $z=0.89$ (look-back time about 7 billion years), consistent with a null result.
--
--   **Formalization Note** The systematic uncertainty $7.0\times10^{-8}$ is an input taken from the paper (it comes from a model of source variability that is not reproduced here). The strict inequalities express "rounds to one decimal in units of $10^{-7}$".
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, Abstract (p. 1) and p. 2 (right column): "we obtain a limit on varying μ to be Δμ/μ = (-0.1 ± 7.6stat ± 7.0sys) ×10^-8 or, if the statistical and systematic uncertainties are added in quadrature, a limit of Δμ/μ = (0.0 ± 1.0)×10^-7."; data from Table 1, p. 4.

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift

theorem combined_limit :
    |muDriftEstimate eK eV eSigma| < 0.05e-7 ∧
      |Real.sqrt (muDriftStatErr eK eSigma ^ 2 + muDriftSysErr ^ 2) - 1.0e-7| < 0.05e-7 := by sorry

end MethanolMuDrift
