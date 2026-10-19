-- Prove2me | Theorems.Thm_Maldacena2003_fNL_eq_tilts
-- name    : Maldacena2003.fNL_eq_tilts
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:52:59.607848+00:00
-- url     : https://prove2.me/theorems/28fe3887-03bd-479a-a9a0-c23a6ae72ef3
-- title:
--   Eq. (4.9): $-f_{NL} = \frac53\frac{\mathcal A}{4\sum_ik_i^3} = -\frac{5}{12}(n_s+f(k)n_t)$
-- statement:
--   Let $\dot\rho_*>0$, $\dot\phi_*\neq0$, $\ddot\phi_*$ real, and let $(k_1,k_2,k_3)$ be a momentum triangle with positive sides. Then
--   $$\frac53\,\frac{\mathcal A}{4\sum_ik_i^3} \;=\; \frac{5}{12}\Big[2\frac{\ddot\phi_*}{\dot\phi_*\dot\rho_*}+\frac{\dot\phi_*^2}{\dot\rho_*^2}\big(2+f(k)\big)\Big] \;=\; -\frac{5}{12}\big(n_s+f(k)\,n_t\big),$$
--   where $\mathcal A$ is the amplitude (4.6), $f(k)$ is the shape function of (4.9), and $n_s$, $n_t$ are the scalar and tensor tilts (2.22), (2.30).
--
--   This expresses the paper's $k$-dependent $f_{NL}$ through the two observable tilts and a purely geometric shape function of the momentum triangle.
--
--   **Formalization Note** The shape function `shapeF` is defined so that the first equality holds. The content of the statement is the consistency of that definition with $\mathcal A$ and the second equality with the tilts.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), p. 18, eq. (4.9)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem fNL_eq_tilts (ρd φd φdd k₁ k₂ k₃ : ℝ) (hρ : 0 < ρd) (hφ : φd ≠ 0)
    (hk : IsMomentumTriangle k₁ k₂ k₃) :
    (5 / 3) * (amplitudeA ρd φd φdd k₁ k₂ k₃ / (4 * (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3)))
        = (5 / 12) * (2 * (φdd / (φd * ρd)) + φd ^ 2 / ρd ^ 2 * (2 + shapeF k₁ k₂ k₃)) ∧
      (5 / 12) * (2 * (φdd / (φd * ρd)) + φd ^ 2 / ρd ^ 2 * (2 + shapeF k₁ k₂ k₃))
        = -(5 / 12) * (scalarTilt ρd φd φdd + shapeF k₁ k₂ k₃ * tensorTilt ρd φd) := by sorry

end Maldacena2003
