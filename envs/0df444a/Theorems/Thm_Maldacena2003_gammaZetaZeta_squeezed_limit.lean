-- Prove2me | Theorems.Thm_Maldacena2003_gammaZetaZeta_squeezed_limit
-- name    : Maldacena2003.gammaZetaZeta_squeezed_limit
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:55:24.985978+00:00
-- url     : https://prove2.me/theorems/3a7e8a1a-b4c0-4ec6-9655-51c8ea6a2756
-- title:
--   Eqs. (4.10) → (4.12): squeezed limit of $\langle\gamma^s_{\vec k_1}\zeta_{\vec k_2}\zeta_{\vec k_3}\rangle$
-- statement:
--   Let $\hat n\in\mathbb R^3$ be a unit vector and $\vec k_2\ne0$, with $k_2=|\vec k_2|$. Let $\epsilon$ be a real symmetric traceless $3\times3$ matrix that is transverse to $\hat n$ ($\epsilon\hat n=0$), i.e. a polarization tensor for a graviton of momentum along $\hat n$. Let $\dot\rho_*,\dot\phi_*$ be real. Put $\vec k_1=t\hat n$ and $\vec k_3=-\vec k_1-\vec k_2$. Then, with $B_{\gamma\zeta\zeta}$ the correlator (4.10),
--   $$\lim_{t\to0^+}\,2t^3\,B_{\gamma\zeta\zeta}(\vec k_1,\vec k_2,\vec k_3) \;=\; \frac{1}{2k_2^5}\,\frac{\dot\rho_*^4}{\dot\phi_*^2}\,2\dot\rho_*^2\,\frac32\,\epsilon_{ij}k_2^ik_2^j .$$
--   Here $2t^3 = 2k_1^3$ cancels the factor $\frac{1}{2k_1^3}$ of the soft graviton's power spectrum.
--
--   This is the statement that the general formula (4.10) agrees with the soft-graviton form (4.12) in the overlapping region, which the paper presents as a consistency check of the computation.
--
--   **Formalization Note** $M_{pl}=1$, and the horizon-crossing times $*$, $*'$ are identified at leading order. Vectors live in `EuclideanSpace ℝ (Fin 3)`.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), pp. 18–19, eqs. (4.10)–(4.12)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem gammaZetaZeta_squeezed_limit (ρd φd : ℝ) (n k₂ : EuclideanSpace ℝ (Fin 3))
    (hn : ‖n‖ = 1) (hk₂ : k₂ ≠ 0) (ε : Matrix (Fin 3) (Fin 3) ℝ)
    (hεsymm : ∀ i j, ε i j = ε j i) (hεtr : Matrix.trace ε = 0)
    (hεtv : ∀ i, ∑ j, ε i j * n j = 0) :
    Tendsto (fun t : ℝ => 2 * t ^ 3 * gammaZetaZetaBispectrum ρd φd ε (t • n) k₂ (-(t • n) - k₂))
      (𝓝[>] 0)
      (𝓝 (1 / (2 * ‖k₂‖ ^ 5) * (ρd ^ 4 / φd ^ 2) * (2 * ρd ^ 2) * (3 / 2)
        * ∑ i, ∑ j, ε i j * k₂ i * k₂ j)) := by sorry

end Maldacena2003
