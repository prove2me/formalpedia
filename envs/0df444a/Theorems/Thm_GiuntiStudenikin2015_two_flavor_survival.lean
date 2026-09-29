-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_two_flavor_survival
-- name    : GiuntiStudenikin2015.two_flavor_survival
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T13:52:19.386274+00:00
-- url     : https://prove2.me/theorems/5d7b6e2a-10d2-44d8-8ce7-f490e4232779
-- title:
--   Two-neutrino survival probability $1-\sin^2 2\vartheta\,\sin^2(\Delta m^2L/4E)$
-- statement:
--   Under the assumptions of Eq. (2.39) ($0\le\vartheta\le\pi/2$, masses $m_1,m_2$, $\Delta m^2=m_2^2-m_1^2$, $L\in\mathbb R$, $E>0$, two-neutrino mixing matrix (2.38)), for each flavor $\ell$
--   $$P_{\nu_\ell\to\nu_\ell}(L,E)=1-\sin^2 2\vartheta\;\sin^2\!\Bigl(\frac{\Delta m^2L}{4E}\Bigr).$$
--
--   Together with (2.39) this shows that probability is conserved in two-neutrino oscillations.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, p. 536, Sec. II.D, Eq. (2.40)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem two_flavor_survival (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2) (m : Fin 2 → ℝ)
    (L E : ℝ) (hE : 0 < E) (l : Fin 2) :
    oscProb (twoFlavorMixing θ) m L E l l =
      1 - Real.sin (2 * θ) ^ 2 * Real.sin ((m 1 ^ 2 - m 0 ^ 2) * L / (4 * E)) ^ 2 := by sorry
end GiuntiStudenikin2015
