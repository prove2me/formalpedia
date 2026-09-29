-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_spin_flavor_precession_matter
-- name    : GiuntiStudenikin2015.spin_flavor_precession_matter
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:10:31.44361+00:00
-- url     : https://prove2.me/theorems/cf1e5a81-101c-4e46-a7e0-98841354246d
-- title:
--   Neutrino spin precession in matter at constant density and field
-- statement:
--   Let $V,\mu,B_\perp\in\mathbb R$ be constant, $\Delta E_{\rm M}=\sqrt{V^2+(2\mu B_\perp)^2}$ and $\sin2\xi=2\mu B_\perp/\Delta E_{\rm M}$. Let $x\mapsto(\psi_L(x),\psi_R(x))\in\mathbb C^2$ be any differentiable solution of
--   $$i\frac{d}{dx}\begin{pmatrix}\psi_L\\\psi_R\end{pmatrix}=\begin{pmatrix}V&\mu B_\perp\\\mu B_\perp&0\end{pmatrix}\begin{pmatrix}\psi_L\\\psi_R\end{pmatrix},\qquad\begin{pmatrix}\psi_L(0)\\\psi_R(0)\end{pmatrix}=\begin{pmatrix}1\\0\end{pmatrix}.$$
--   Then for every $x$
--   $$P_{\nu_L\to\nu_R}(x)=|\psi_R(x)|^2=\Bigl(\frac{2\mu B_\perp}{\Delta E_{\rm M}}\Bigr)^2\sin^2\!\Bigl(\frac{\Delta E_{\rm M}\,x}{2}\Bigr)=\sin^2 2\xi\;\sin^2\!\bigl(\tfrac12\Delta E_{\rm M}x\bigr).$$
--
--   Since $\Delta E_{\rm M}>2\mu B_\perp$ when $V\ne0$, matter suppresses the amplitude of $\nu_L\to\nu_R$ transitions.
--
--   **Formalization Note** In the degenerate case $V=\mu B_\perp=0$ the quotient $2\mu B_\perp/\Delta E_{\rm M}$ is $0/0$, which Lean evaluates to $0$; both sides are then $0$.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, p. 566, Sec. VI.B, Eqs. (6.28)–(6.34)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem spin_flavor_precession_matter (V μ B : ℝ) (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ x : ℝ, HasDerivAt ψ (-(Complex.I • (spinFlavorHamiltonian V μ B).mulVec (ψ x))) x)
    (h0 : ψ 0 = ![1, 0]) (x : ℝ) :
    Complex.normSq (ψ x 1) =
      (2 * μ * B / spinFlavorEnergySplitting V μ B) ^ 2 *
        Real.sin (spinFlavorEnergySplitting V μ B * x / 2) ^ 2 := by sorry
end GiuntiStudenikin2015
