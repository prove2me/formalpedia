-- Prove2me | Theorems.Thm_NymanBeurling_fixed_damping_shifted_boundary_zero
-- name    : NymanBeurling.fixed_damping_shifted_boundary_zero
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:45:30.655879+00:00
-- url     : https://prove2.me/theorems/ab45b2f8-9645-4500-b2fc-295e44b82eb3
-- title:
--   Fixed damping forces a matching critical-line zero at the shifted boundary
-- statement:
--   Fix $0<\varepsilon<1/2$ and suppose the prefix energies of the finite damped Möbius residuals are uniformly bounded:
--   $$
--   \sup_{N,H}\sum_{m=1}^H
--     \frac{\lvert R_{N,\varepsilon}(m)\rvert^2}{m(m+1)}<\infty.
--   $$
--   If $\zeta(\rho)=0$ at the shifted boundary $\Re\rho=1/2+\varepsilon$, then $\zeta(\rho-\varepsilon)=0$. Thus any boundary zero has a critical-line zero at the same ordinate. Bounded energies already exclude all zeros strictly to the right of this boundary.
-- source:
--   Boundary strengthening of NymanBeurling.fixed_damping_bounded_energy_implies_shifted_zero_free, https://prove2.me/theorems/baa66214-985e-45bb-8cca-c47070b7cd0c. The weighted Hilbert–Mellin model is from B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), pp. 137–146, https://arxiv.org/abs/math/0607733.

import Mathlib
import Definitions.Def_NymanBeurling_DampedResidualLimits

open NymanBeurling
open scoped BigOperators

theorem NymanBeurling.fixed_damping_shifted_boundary_zero
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2)
    (hB : ∃ B : ℝ, ∀ N H : ℕ, (∑ n ∈ Finset.range H,
      (dampedResidualFinite N ε (n+1)) ^ 2 / ((n+1 : ℝ) * (n+2 : ℝ))) ≤ B)
    (ρ : ℂ) (hρ : ρ.re = 1/2 + ε) (hzρ : riemannZeta ρ = 0) :
    riemannZeta (ρ-(ε:ℂ)) = 0 := by sorry
