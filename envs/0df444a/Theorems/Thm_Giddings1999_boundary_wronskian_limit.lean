-- Prove2me | Theorems.Thm_Giddings1999_boundary_wronskian_limit
-- name    : Giddings1999.boundary_wronskian_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T01:51:17.412262+00:00
-- url     : https://prove2.me/theorems/6d5f3a6b-fa38-4b88-a78f-734ed228d46b
-- title:
--   Eqs. (19)–(20): $\lim_{r\to\pi/2}(\tan r)^{d-1}[(\cos r)^{2h_-}\overleftrightarrow{\partial_r}(\cos r)^{2h_+}]=-2\nu$
-- statement:
--   Let $d\ge1$ and $m,R\in\mathbb R$. With $A\overleftrightarrow{\partial_r}B=A\,\partial_rB-(\partial_rA)\,B$,
--   $$\lim_{r\to\pi/2^-}(\tan r)^{d-1}\Bigl[(\cos r)^{2h_-}\,\partial_r(\cos r)^{2h_+}-(\cos r)^{2h_+}\,\partial_r(\cos r)^{2h_-}\Bigr]=-2\nu .$$
--
--   This limit converts the surface integral (19) into eq. (20). It fixes the factor $2\nu R^{d-1}$ relating the bulk–boundary propagator to the bulk Feynman propagator (eq. 21), and it recurs in the matrix elements (28)–(29).
-- source:
--   S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eqs. (19), (20), p. 2708

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology

namespace Giddings1999

/-- **Milestone, eqs. (19)–(20)**: the boundary limit
`lim_{r→π/2} (tan r)^{d−1} [(cos r)^{2h₋} ∂⃡_r (cos r)^{2h₊}] = −2ν`, where `A ∂⃡ B = A ∂B − (∂A) B`. -/
theorem boundary_wronskian_limit (d : ℕ) (hd : 1 ≤ d) (m R : ℝ) :
    Tendsto (fun r => tan r ^ (d - 1) *
        (cos r ^ twoHMinus d m R * deriv (fun s => cos s ^ twoHPlus d m R) r
          - cos r ^ twoHPlus d m R * deriv (fun s => cos s ^ twoHMinus d m R) r))
      (𝓝[<] (π / 2)) (𝓝 (-2 * nu d m R)) := by
  sorry

end Giddings1999
