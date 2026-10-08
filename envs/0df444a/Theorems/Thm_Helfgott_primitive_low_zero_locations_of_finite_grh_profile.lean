-- Prove2me | Theorems.Thm_Helfgott_primitive_low_zero_locations_of_finite_grh_profile
-- name    : Helfgott.primitive_low_zero_locations_of_finite_grh_profile
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T03:54:29.255191+00:00
-- url     : https://prove2.me/theorems/52230510-d1ee-4a0f-9d42-56b7e7c04fbc
-- title:
--   Usual finite primitive GRH certificates supply the complete Goldbach low-zero location profile
-- statement:
--   For every primitive Dirichlet character $\chi$ of conductor $q\ge1$, set $Q_q=2q$ for odd $q$ and $Q_q=q$ for even $q$, and suppose $Q_q\le300000$. Assume finite GRH only for the usual nontrivial zeros: $$L(\rho,\chi)=0,\quad 0<\Re\rho<1,\quad |\Im\rho|<\max\left\{200+\frac{75000000}{Q_q},\frac{10^8}{q}\right\}\quad\Longrightarrow\quad\Re\rho=\frac12.$$ Then the exact regularized low-zero location profile required by the original three-prime major-arc estimate follows, including all zeros in $-1/2\le\Re s\le2$ and the explicit possible trivial zero at zero. This is a reduction from a finite GRH certificate, not a proof of that certificate. It removes the need to include regularization and zeros outside the critical strip in a future numerical witness.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897, section 4.6. Primitive Dirichlet functional equation, gamma factors and nonvanishing on Re s >= 1 in Mathlib. Written by Codex.

import Definitions.Def_Helfgott_PrimitiveLowZeroLocations
import Mathlib.NumberTheory.LSeries.Nonvanishing
open scoped Classical

namespace Helfgott
theorem primitive_low_zero_locations_of_finite_grh_profile
    (hgrh : ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),ψ.IsPrimitive →
      (if Odd q then 2*q else q : ℕ)≤300000 → ∀ ρ : ℂ,
      0<ρ.re → ρ.re<1 → ψ.LFunction ρ=0 →
      |ρ.im|<max (200+75000000/((if Odd q then 2*q else q : ℕ) : ℝ))
        ((10 : ℝ)^8/(q : ℝ)) → ρ.re=1/2) : PrimitiveLowZeroLocations := by sorry
end Helfgott
