-- Prove2me | Theorems.Thm_Maldacena2003_tensor_tilt_formula
-- name    : Maldacena2003.tensor_tilt_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:51:14.418864+00:00
-- url     : https://prove2.me/theorems/01cd8c07-b6af-415f-be3d-da51b1eede2a
-- title:
--   Eq. (2.30): $\frac{1}{\dot\rho}\frac{d}{dt}\log\dot\rho^2 = -\frac{\dot\phi^2}{\dot\rho^2}$
-- statement:
--   Let $\rho,\phi:\mathbb R\to\mathbb R$ be $C^2$ and $V:\mathbb R\to\mathbb R$ differentiable, and suppose that for all $s$ the background equations (2.3) hold:
--   $$3\dot\rho^2 = \tfrac12\dot\phi^2+V(\phi),\qquad \ddot\rho=-\tfrac12\dot\phi^2,\qquad \ddot\phi+3\dot\rho\dot\phi+V'(\phi)=0 .$$
--   Let $t$ be a time with $\dot\rho(t)>0$ and $\dot\phi(t)\ne0$. Then
--   $$\frac{1}{\dot\rho(t)}\,\frac{d}{dt}\log\big(\dot\rho^2\big)(t) \;=\; -\frac{\dot\phi(t)^2}{\dot\rho(t)^2} \;=\; n_t .$$
--
--   This is the tensor tilt (2.30). The tensor power spectrum (2.29) is proportional to $\dot\rho_*^2$, and this identity expresses its tilt through the slow-roll factor $\dot\phi_*^2/\dot\rho_*^2$ that appears in (4.9) and (4.14).
--
--   **Formalization Note** Time derivatives are Lean `deriv`; the approximation $k\frac{d}{dk}\sim\frac{1}{\dot\rho}\frac{d}{dt}$ is not formalized.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), p. 9, eq. (2.30) (with background equations (2.3), p. 4)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem tensor_tilt_formula (ρ φ V : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ) (hφ : ContDiff ℝ 2 φ) (hV : Differentiable ℝ V)
    (hfried : ∀ s, 3 * deriv ρ s ^ 2 = deriv φ s ^ 2 / 2 + V (φ s))
    (hrhoddot : ∀ s, deriv (deriv ρ) s = -(deriv φ s ^ 2 / 2))
    (hkg : ∀ s, deriv (deriv φ) s + 3 * deriv ρ s * deriv φ s + deriv V (φ s) = 0)
    (t : ℝ) (hH : 0 < deriv ρ t) (hφd : deriv φ t ≠ 0) :
    (1 / deriv ρ t) * deriv (fun s => Real.log (deriv ρ s ^ 2)) t
      = tensorTilt (deriv ρ t) (deriv φ t) := by sorry

end Maldacena2003
