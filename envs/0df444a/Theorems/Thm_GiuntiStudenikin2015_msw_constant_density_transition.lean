-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_msw_constant_density_transition
-- name    : GiuntiStudenikin2015.msw_constant_density_transition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:31:57.624901+00:00
-- url     : https://prove2.me/theorems/d08ebc1f-6827-461c-9665-c8622ff5ccbc
-- title:
--   MSW transition probability at constant matter density
-- statement:
--   Let $\Delta m^2,V_{\rm CC}\in\mathbb R$ (constant matter density), $0\le\vartheta\le\pi/2$ and $E>0$, and let $\mathrm H$, $\Delta m^2_{\rm M}$, $\vartheta_{\rm M}$ be as in (2.46), (2.53), (2.54). Let $x\mapsto(\varphi_e(x),\varphi_a(x))\in\mathbb C^2$ be any differentiable solution of
--   $$i\frac{d}{dx}\begin{pmatrix}\varphi_e\\\varphi_a\end{pmatrix}=\mathrm H\begin{pmatrix}\varphi_e\\\varphi_a\end{pmatrix},\qquad\begin{pmatrix}\varphi_e(0)\\\varphi_a(0)\end{pmatrix}=\begin{pmatrix}1\\0\end{pmatrix}.$$
--   Then for every $x$
--   $$P_{\nu_e\to\nu_a}(x)=|\varphi_a(x)|^2=\sin^2 2\vartheta_{\rm M}\;\sin^2\!\Bigl(\frac{\Delta m^2_{\rm M}\,x}{4E}\Bigr).$$
--
--   This is the matter analogue of (2.39), with the vacuum mixing angle and squared-mass difference replaced by their effective values in matter.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, pp. 536–537, Sec. II.D, Eqs. (2.44)–(2.49), (2.53)–(2.54), (2.57)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem msw_constant_density_transition (dm2 θ E Vcc : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2)
    (hE : 0 < E) (φ : ℝ → Fin 2 → ℂ)
    (hφ : ∀ x : ℝ, HasDerivAt φ (-(Complex.I • (mswHamiltonian dm2 θ E Vcc).mulVec (φ x))) x)
    (h0 : φ 0 = ![1, 0]) (x : ℝ) :
    Complex.normSq (φ x 1) =
      Real.sin (2 * mswMixingAngle dm2 θ E Vcc) ^ 2 *
        Real.sin (mswDeltaM2 dm2 θ E Vcc * x / (4 * E)) ^ 2 := by sorry
end GiuntiStudenikin2015
