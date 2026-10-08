-- Prove2me | Theorems.Thm_LariviereIGFR_Char_igfr_iff_log_ifr
-- name    : LariviereIGFR.Char.igfr_iff_log_ifr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:02.008384+00:00
-- url     : https://prove2.me/theorems/ee005986-885b-43c5-8c99-ac4ebcfb211e
-- title:
--   Proof of Theorem 1, p. 603 — parts 1 ⇔ 2: X is IGFR iff X_L = log X is IFR
-- statement:
--   Let $X \ge 0$ have law $\mu$ with regular density $\varphi$, and let $X_L = \log X$, with density $\varphi_L(\xi) = e^{\xi}\varphi(e^{\xi})$. Then
--   $$X \text{ is IGFR} \iff X_L \text{ is IFR}.$$
--   Here IGFR means that $g(\xi) = \xi\varphi(\xi)/\bar\Phi(\xi)$ is weakly increasing on $\{\Phi < 1\}$, and IFR means that $h_L(\xi) = \varphi_L(\xi)/\bar\Phi_L(\xi)$ is weakly increasing on $\{\Phi_L < 1\}$.
--
--   This is the equivalence of parts 1 and 2 of Theorem 1: it lets every known property of IFR laws be transferred to IGFR laws through the logarithm.
--
--   **Formalization Note** $X_L$ is the image of $\mu$ under `Real.log`, never a hand-written function of $\Phi$, so the equivalence has content.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §2, proof of Theorem 1 ("which establishes the equivalence of parts 1 and 2")

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem igfr_iff_log_ifr (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    IsIGFR μ φ ↔ IsIFR (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)) := by sorry

end LariviereIGFR.Char
