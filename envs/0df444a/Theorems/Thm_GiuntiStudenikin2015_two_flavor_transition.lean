-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_two_flavor_transition
-- name    : GiuntiStudenikin2015.two_flavor_transition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T13:22:23.80626+00:00
-- url     : https://prove2.me/theorems/00c7ff09-30f6-4e2a-9e29-9a0667bfceff
-- title:
--   Two-neutrino transition probability $\sin^2 2\vartheta\,\sin^2(\Delta m^2L/4E)$
-- statement:
--   Let $0\le\vartheta\le\pi/2$, let $m_1,m_2\in\mathbb R$ be the two neutrino masses with $\Delta m^2=m_2^2-m_1^2$, let $L\in\mathbb R$ and $E>0$. With the two-neutrino mixing matrix $U=\begin{pmatrix}\cos\vartheta&\sin\vartheta\\-\sin\vartheta&\cos\vartheta\end{pmatrix}$ and the plane-wave probability $P_{\ell\to\ell'}$ of Eqs. (2.35)–(2.36), for the two distinct flavors $\ell\ne\ell'$
--   $$P_{\nu_\ell\to\nu_{\ell'}}(L,E)=\sin^2 2\vartheta\;\sin^2\!\Bigl(\frac{\Delta m^2L}{4E}\Bigr).$$
--
--   This is the standard fitting function for two-flavor oscillation experiments.
--
--   **Formalization Note** The masses are indexed by `0,1`, standing for the paper's $\nu_1,\nu_2$.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, p. 536, Sec. II.D, Eqs. (2.38)–(2.39)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem two_flavor_transition (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2) (m : Fin 2 → ℝ)
    (L E : ℝ) (hE : 0 < E) (l l' : Fin 2) (hll' : l ≠ l') :
    oscProb (twoFlavorMixing θ) m L E l l' =
      Real.sin (2 * θ) ^ 2 * Real.sin ((m 1 ^ 2 - m 0 ^ 2) * L / (4 * E)) ^ 2 := by sorry
end GiuntiStudenikin2015
