-- Prove2me | Theorems.Thm_MethanolMuDrift_allLine_fit
-- name    : MethanolMuDrift.allLine_fit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T22:55:22.23588+00:00
-- url     : https://prove2.me/theorems/b501478e-f2bd-452c-a94c-8ff24fd3a45b
-- title:
--   Fit of all four lines: $\Delta\mu/\mu=(11.0\pm6.8)\times10^{-8}$, $\chi^2_\nu\approx6.4$
-- statement:
--   Fit a straight line, by weighted least squares with weights $1/\sigma_i^2$, to all four methanol lines of Table 1 plotted against their sensitivity coefficients:
--   $$(K_\mu,\,V\pm\sigma)\in\{(-32.8,\,9.06\pm0.67),\,(-1,\,8.40\pm0.10),\,(-1,\,9.12\pm0.30),\,(-7.4,\,9.83\pm0.43)\}\quad(\text{km/s}).$$
--   With slope $b$, slope standard error $\sigma_b$ and reduced chi-squared $\chi^2_\nu$ (two degrees of freedom),
--   $$\Big|{-\tfrac{b}{c}}-11.0\times10^{-8}\Big|\le0.5\times10^{-8},\qquad\Big|\tfrac{\sigma_b}{c}-6.8\times10^{-8}\Big|\le0.1\times10^{-8},\qquad|\chi^2_\nu-6.4|\le0.2 .$$
--   This corresponds to the paper's four-line result $\Delta\mu/\mu=(11.0\pm6.8)\times10^{-8}$ with "a much larger $\chi^2_\nu$ of 6.4", which motivated discarding the A line from the fiducial fit.
--
--   **Formalization Note** Recomputation from the rounded Table 1 entries gives $\approx11.35\times10^{-8}$, $\approx6.84\times10^{-8}$ and $\chi^2_\nu\approx6.27$, slightly different from the printed values (presumably computed from unrounded positions). The tolerances $0.5\times10^{-8}$, $0.1\times10^{-8}$ and $0.2$ were chosen to cover this rounding gap; they are a formalization choice, not stated in the paper.
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, p. 2 (left column): "The fit on all four transitions has a much larger χν² of 6.4 ... and it delivers Δμ/μ = (11.0 ± 6.8) × 10^-8."; data from Table 1, p. 4.

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift

theorem allLine_fit :
    |muDriftEstimate allK allV allSigma - 11.0e-8| ≤ 0.5e-8 ∧
      |muDriftStatErr allK allSigma - 6.8e-8| ≤ 0.1e-8 ∧
      |wlsReducedChiSq allK allV allSigma - 6.4| ≤ 0.2 := by sorry

end MethanolMuDrift
