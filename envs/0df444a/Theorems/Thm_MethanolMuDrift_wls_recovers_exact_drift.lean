-- Prove2me | Theorems.Thm_MethanolMuDrift_wls_recovers_exact_drift
-- name    : MethanolMuDrift.wls_recovers_exact_drift
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T21:36:13.893449+00:00
-- url     : https://prove2.me/theorems/15f0e8a3-aa06-4683-8d2e-cdc081c4f877
-- title:
--   The line fit of $V$ against $K_\mu$ recovers $\Delta\mu/\mu$ from noise-free data
-- statement:
--   Let $n$ points carry sensitivity coefficients $K_1,\dots,K_n$ and nonzero uncertainties $\sigma_1,\dots,\sigma_n$, and assume the $K_i$ are not all equal. Suppose the line positions obey the paper's velocity relation $V/c=-K_\mu\,\Delta\mu/\mu$ exactly, up to a common velocity offset $a$:
--   $$V_i = a - c\,\delta\,K_i\qquad(i=1,\dots,n),$$
--   where $\delta$ plays the role of $\Delta\mu/\mu$. Then the weighted least-squares straight-line fit of $V$ against $K_\mu$ (weights $1/\sigma_i^2$) returns exactly these parameters: the derived estimate $-b/c$ equals $\delta$ and the fitted intercept equals $a$,
--   $$-\frac{b}{c}=\delta,\qquad a_{\mathrm{fit}}=a .$$
--   This is the consistency property behind Fig. 3: fitting a line to the observed positions plotted against $K_\mu$ and reading off its slope measures $\Delta\mu/\mu$.
--
--   **Formalization Note** The uncertainties only need to be nonzero (weights $1/\sigma_i^2>0$); the non-constancy of $K$ guarantees that the normal equations are nondegenerate. Velocities and $c$ are in km/s.
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, p. 2 (left column): "The velocities between different transitions are interrelated via V/c = -KμΔμ/μ ... to determine the fractional change in μ, the peak positions of the four transitions are plotted (in V/c) versus Kμ, and a (dashed) line is fitted to the data (Fig. 3)."

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift

theorem wls_recovers_exact_drift {n : ℕ} (K σ : Fin n → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (hK : ∃ i j, K i ≠ K j) (a δ : ℝ) :
    muDriftEstimate K (fun i => a - speedOfLight * δ * K i) σ = δ ∧
      wlsIntercept K (fun i => a - speedOfLight * δ * K i) σ = a := by sorry

end MethanolMuDrift
