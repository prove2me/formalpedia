-- Prove2me | Theorems.Thm_MethanolMuDrift_eLine_fit
-- name    : MethanolMuDrift.eLine_fit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T22:00:06.284395+00:00
-- url     : https://prove2.me/theorems/66886b80-4d85-4740-9845-1c3b09296405
-- title:
--   Fit of the three E lines: $\Delta\mu/\mu=(-0.1\pm7.6)\times10^{-8}$, $\chi^2_\nu\approx2.0$
-- statement:
--   Fit a straight line, by weighted least squares with weights $1/\sigma_i^2$, to the positions of the three E-symmetry methanol lines of Table 1 plotted against their sensitivity coefficients:
--   $$(K_\mu,\,V\pm\sigma)\in\{(-32.8,\;9.06\pm0.67),\;(-1,\;9.12\pm0.30),\;(-7.4,\;9.83\pm0.43)\}\quad(\text{km/s}).$$
--   Let $b$ be the fitted slope, $\sigma_b$ its standard error and $\chi^2_\nu$ the reduced chi-squared (one degree of freedom). Then the derived estimate $\Delta\mu/\mu=-b/c$, its statistical error $\sigma_b/c$ and $\chi^2_\nu$ reproduce the paper's values to the stated precision:
--   $$\Big|{-\tfrac{b}{c}}-(-0.1\times10^{-8})\Big|\le0.05\times10^{-8},\qquad \Big|\tfrac{\sigma_b}{c}-7.6\times10^{-8}\Big|\le0.1\times10^{-8},\qquad |\chi^2_\nu-2.0|\le0.05 .$$
--   This is the paper's fiducial measurement $\Delta\mu/\mu=(-0.1\pm7.6)\times10^{-8}$ with $\chi^2_\nu\sim2.0$.
--
--   **Formalization Note** The paper reports rounded values computed from unrounded data; recomputation from the rounded Table 1 entries gives $\sigma_b/c\approx7.69\times10^{-8}$, so the tolerance on the error is $0.1\times10^{-8}$ rather than a half unit of the last digit. Tolerances on the estimate and on $\chi^2_\nu$ are a half unit of the last reported digit.
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, p. 2 (left column): "The analysis of the E transitions results in Δμ/μ = (-0.1 ± 7.6)×10^-8 ... The reduced chi-squared, χν², ... is ~2.0"; data from Table 1, p. 4.

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift

theorem eLine_fit :
    |muDriftEstimate eK eV eSigma - (-0.1e-8)| ≤ 0.05e-8 ∧
      |muDriftStatErr eK eSigma - 7.6e-8| ≤ 0.1e-8 ∧
      |wlsReducedChiSq eK eV eSigma - 2.0| ≤ 0.05 := by sorry

end MethanolMuDrift
