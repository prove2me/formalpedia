-- Prove2me | Theorems.Thm_Maldacena2003_scalar_tilt_formula
-- name    : Maldacena2003.scalar_tilt_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:50:44.31116+00:00
-- url     : https://prove2.me/theorems/2997277b-6814-4371-a904-740f9487bf19
-- title:
--   Eq. (2.22): $\frac{1}{\dot\rho}\frac{d}{dt}\log\frac{\dot\rho^4}{\dot\phi^2} = -2\big(\frac{\ddot\phi}{\dot\rho\dot\phi}+\frac{\dot\phi^2}{\dot\rho^2}\big)$
-- statement:
--   Let $\rho,\phi:\mathbb R\to\mathbb R$ be $C^2$ and $V:\mathbb R\to\mathbb R$ differentiable, and suppose that for all $s$ the background equations (2.3) hold:
--   $$3\dot\rho^2 = \tfrac12\dot\phi^2+V(\phi),\qquad \ddot\rho=-\tfrac12\dot\phi^2,\qquad \ddot\phi+3\dot\rho\dot\phi+V'(\phi)=0 .$$
--   Let $t$ be a time with $\dot\rho(t)>0$ and $\dot\phi(t)\ne0$. Then
--   $$\frac{1}{\dot\rho(t)}\,\frac{d}{dt}\log\!\Big(\frac{\dot\rho^4}{\dot\phi^2}\Big)(t) \;=\; -2\Big(\frac{\ddot\phi(t)}{\dot\rho(t)\dot\phi(t)}+\frac{\dot\phi(t)^2}{\dot\rho(t)^2}\Big) \;=\; n_s .$$
--
--   This is the exact part of the scalar tilt formula (2.22). The power spectrum (2.20) is proportional to $\dot\rho_*^4/\dot\phi_*^2$, so this identity converts the time dependence of the horizon-crossing values into the scalar tilt $n_s$ used in (4.7) and (4.9).
--
--   **Formalization Note** Time derivatives are Lean `deriv`. The printed (2.22) has $\dot\phi_*/\dot\rho_*$ where $\dot\phi_*^2/\dot\rho_*^2$ is meant; the corrected form is stated. Only the exact identity is formalized, not the approximation $k\frac{d}{dk}\sim\frac{1}{\dot\rho}\frac{d}{dt}$.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), p. 7, eq. (2.22) (with background equations (2.3), p. 4)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem scalar_tilt_formula (ρ φ V : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ) (hφ : ContDiff ℝ 2 φ) (hV : Differentiable ℝ V)
    (hfried : ∀ s, 3 * deriv ρ s ^ 2 = deriv φ s ^ 2 / 2 + V (φ s))
    (hrhoddot : ∀ s, deriv (deriv ρ) s = -(deriv φ s ^ 2 / 2))
    (hkg : ∀ s, deriv (deriv φ) s + 3 * deriv ρ s * deriv φ s + deriv V (φ s) = 0)
    (t : ℝ) (hH : 0 < deriv ρ t) (hφd : deriv φ t ≠ 0) :
    (1 / deriv ρ t) * deriv (fun s => Real.log (deriv ρ s ^ 4 / deriv φ s ^ 2)) t
      = scalarTilt (deriv ρ t) (deriv φ t) (deriv (deriv φ) t) := by sorry

end Maldacena2003
