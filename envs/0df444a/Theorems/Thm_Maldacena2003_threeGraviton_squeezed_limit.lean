-- Prove2me | Theorems.Thm_Maldacena2003_threeGraviton_squeezed_limit
-- name    : Maldacena2003.threeGraviton_squeezed_limit
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:57:05.82834+00:00
-- url     : https://prove2.me/theorems/b165adbc-de24-42a6-8fad-91ddf631dd53
-- title:
--   Eqs. (4.15) → (4.17): squeezed limit of $\langle\gamma^{s_1}\gamma^{s_2}\gamma^{s_3}\rangle$
-- statement:
--   Let $\hat n\in\mathbb R^3$ be a unit vector and $\vec k_2\ne0$, with $k_2=|\vec k_2|$. Let $\epsilon^1,\epsilon^2,\epsilon^3$ be real symmetric traceless $3\times3$ matrices with $\epsilon^1\hat n=0$, $\epsilon^2\vec k_2=0$ and $\epsilon^3\vec k_2=0$. These are the polarizations of the soft graviton and of the two hard gravitons, the latter in the limiting configuration $\vec k_3\to-\vec k_2$. Let $\dot\rho_*$ be real. Put $\vec k_1=t\hat n$ and $\vec k_3=-\vec k_1-\vec k_2$. Then, with $B_{\gamma\gamma\gamma}$ the correlator (4.15),
--   $$\lim_{t\to0^+}2t^3\,B_{\gamma\gamma\gamma}(\vec k_1,\vec k_2,\vec k_3) \;=\; \big(\epsilon^2_{ij}\epsilon^3_{ij}\big)\,\dot\rho_*^2\,\frac{1}{2k_2^5}\,2\dot\rho_*^2\,\frac32\,\epsilon^1_{ij}k_2^ik_2^j .$$
--
--   For equal hard polarizations, $\epsilon^2_{ij}\epsilon^3_{ij}=2\delta_{s_2s_3}$, and the right-hand side is the coefficient in (4.17). The statement is the agreement of (4.15) with (4.17) in the overlapping region.
--
--   **Formalization Note** $M_{pl}=1$, and the horizon-crossing times $*$, $*'$ are identified at leading order. The polarizations are held fixed along the limit, and the hard polarizations are taken transverse to $\vec k_2$, the limiting direction of $\pm\vec k_3$.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), pp. 19–20, eqs. (4.15)–(4.17)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem threeGraviton_squeezed_limit (ρd : ℝ) (n k₂ : EuclideanSpace ℝ (Fin 3))
    (hn : ‖n‖ = 1) (hk₂ : k₂ ≠ 0) (ε₁ ε₂ ε₃ : Matrix (Fin 3) (Fin 3) ℝ)
    (hε₁symm : ∀ i j, ε₁ i j = ε₁ j i) (hε₁tr : Matrix.trace ε₁ = 0)
    (hε₁tv : ∀ i, ∑ j, ε₁ i j * n j = 0)
    (hε₂symm : ∀ i j, ε₂ i j = ε₂ j i) (hε₂tr : Matrix.trace ε₂ = 0)
    (hε₂tv : ∀ i, ∑ j, ε₂ i j * k₂ j = 0)
    (hε₃symm : ∀ i j, ε₃ i j = ε₃ j i) (hε₃tr : Matrix.trace ε₃ = 0)
    (hε₃tv : ∀ i, ∑ j, ε₃ i j * k₂ j = 0) :
    Tendsto
      (fun t : ℝ => 2 * t ^ 3 * threeGravitonBispectrum ρd ε₁ ε₂ ε₃ (t • n) k₂ (-(t • n) - k₂))
      (𝓝[>] 0)
      (𝓝 ((∑ i, ∑ j, ε₂ i j * ε₃ i j) * ρd ^ 2 * (1 / (2 * ‖k₂‖ ^ 5)) * (2 * ρd ^ 2) * (3 / 2)
        * ∑ i, ∑ j, ε₁ i j * k₂ i * k₂ j)) := by sorry

end Maldacena2003
