-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_spin_precession_vacuum
-- name    : GiuntiStudenikin2015.spin_precession_vacuum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:08:55.177804+00:00
-- url     : https://prove2.me/theorems/7e66e50b-7816-4b80-b89f-2ae30aa680f9
-- title:
--   Neutrino spin precession in a transverse magnetic field
-- statement:
--   Let $\mu\in\mathbb R$ be the neutrino magnetic moment and $B_\perp:\mathbb R\to\mathbb R$ a continuous transverse magnetic field profile. Let $x\mapsto(\psi_L(x),\psi_R(x))\in\mathbb C^2$ be any differentiable solution of
--   $$i\frac{d}{dx}\begin{pmatrix}\psi_L\\\psi_R\end{pmatrix}=\begin{pmatrix}0&\mu B_\perp(x)\\\mu B_\perp(x)&0\end{pmatrix}\begin{pmatrix}\psi_L\\\psi_R\end{pmatrix},\qquad\begin{pmatrix}\psi_L(0)\\\psi_R(0)\end{pmatrix}=\begin{pmatrix}1\\0\end{pmatrix}.$$
--   Then for every $x$
--   $$P_{\nu_L\to\nu_R}(x)=|\psi_R(x)|^2=\sin^2\!\Bigl(\int_0^x\mu B_\perp(x')\,dx'\Bigr).$$
--
--   The transition probability is independent of the neutrino energy, and complete $\nu_L\to\nu_R$ conversion occurs when the integral equals $\pi/2$.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, pp. 565–566, Sec. VI.B, Eqs. (6.23)–(6.27)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem spin_precession_vacuum (μ : ℝ) (B : ℝ → ℝ) (hB : Continuous B)
    (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ x : ℝ, HasDerivAt ψ (-(Complex.I • (spinFlavorHamiltonian 0 μ (B x)).mulVec (ψ x))) x)
    (h0 : ψ 0 = ![1, 0]) (x : ℝ) :
    Complex.normSq (ψ x 1) = Real.sin (∫ t in (0 : ℝ)..x, μ * B t) ^ 2 := by sorry
end GiuntiStudenikin2015
