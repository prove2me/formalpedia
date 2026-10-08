-- Prove2me | Theorems.Thm_Helfgott_actual_primitive_finite_grh_profile
-- name    : Helfgott.actual_primitive_finite_grh_profile
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-06T03:54:36.072073+00:00
-- url     : https://prove2.me/theorems/2a396125-2b12-4e6a-ad1b-84127eb18372
-- title:
--   Finite primitive GRH witness at the exact three-prime Goldbach major-arc heights
-- statement:
--   For every primitive Dirichlet character $\chi$ of conductor $q\ge1$, put $Q_q=2q$ for odd $q$ and $Q_q=q$ for even $q$, and require $Q_q\le300000$. Establish the finite GRH statement $$L(\rho,\chi)=0,\quad 0<\Re\rho<1,\quad |\Im\rho|<\max\left\{200+\frac{75000000}{Q_q},\frac{10^8}{q}\right\}\quad\Longrightarrow\quad\Re\rho=\frac12.$$ Thus the needed conductors are odd $q\le150000$ and even $q\le300000$. This is the remaining numerical zero-location witness for the new direct major-arc reduction. All smoothing-weighted low-zero masses, high-zero tails and retained-contour errors are handled separately by proved analytic estimates; they are not hypotheses of this witness. A solution must justify the finite zero-location certification. No external numerical computation or finite GRH assertion is assumed proved in this statement.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897, section 4.6. This is an Open numerical witness obligation, and no proof is supplied here. Written by Codex.

import Mathlib.NumberTheory.LSeries.Nonvanishing
open scoped Classical

namespace Helfgott
theorem actual_primitive_finite_grh_profile :
  ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),ψ.IsPrimitive →
      (if Odd q then 2*q else q : ℕ)≤300000 → ∀ ρ : ℂ,
      0<ρ.re → ρ.re<1 → ψ.LFunction ρ=0 →
      |ρ.im|<max (200+75000000/((if Odd q then 2*q else q : ℕ) : ℝ))
        ((10 : ℝ)^8/(q : ℝ)) → ρ.re=1/2 := by sorry
end Helfgott
