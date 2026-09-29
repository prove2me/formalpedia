-- Prove2me | Theorems.Thm_GFactorPhysics_muon_E821_discrepancy
-- name    : GFactorPhysics.muon_E821_discrepancy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:49:35.541363+00:00
-- url     : https://prove2.me/theorems/c45d0703-8116-4efe-ae9c-4c83415461de
-- title:
--   E821 muon g-factor: experiment and theory differ by between 3.4 and 3.5 standard deviations
-- statement:
--   The E821 final report quoted the measured muon g-factor $g_{\exp} = -2.002\,331\,8416(13)$ and the theoretical prediction $g_{\mathrm{th}} = -2.002\,331\,836\,20(86)$, i.e. standard uncertainties $\sigma_{\exp}=1.3\times10^{-9}$ and $\sigma_{\mathrm{th}}=8.6\times10^{-10}$. Combining the two uncertainties in quadrature,
--
--   $$3.4 \;\le\; \frac{|g_{\exp}-g_{\mathrm{th}}|}{\sqrt{\sigma_{\exp}^2+\sigma_{\mathrm{th}}^2}} \;<\; 3.5 .$$
--
--   This checks the article's statement that the two values differ by 3.4 standard deviations (the exact quotient is about $3.46$).
--
--   **Formalization Note** The article does not say how the two uncertainties are combined; quadrature (independent errors) is the standard convention and is what is formalized. The article's "3.4" is read as the quotient truncated to one decimal.
-- source:
--   Wikipedia, "g-factor (physics)" (PDF snapshot supplied by the user, `G-factor_(physics).pdf`), https://en.wikipedia.org/wiki/G-factor_(physics); section "Muon g-factor": "the experimental measured value is −2.002 331 8416(13), compared to the theoretical prediction of −2.002 331 836 20(86). This is a difference of 3.4 standard deviations".

import Mathlib

namespace GFactorPhysics
theorem muon_E821_discrepancy :
    (3.4 : ℝ) ≤ |(-2.0023318416 : ℝ) - (-2.00233183620)| /
        Real.sqrt ((1.3e-9 : ℝ) ^ 2 + (8.6e-10 : ℝ) ^ 2) ∧
      |(-2.0023318416 : ℝ) - (-2.00233183620)| /
        Real.sqrt ((1.3e-9 : ℝ) ^ 2 + (8.6e-10 : ℝ) ^ 2) < 3.5 := by sorry
end GFactorPhysics
