-- Prove2me | Theorems.Thm_Giddings1999_twoH_indicial_roots
-- name    : Giddings1999.twoH_indicial_roots
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T01:48:33.776322+00:00
-- url     : https://prove2.me/theorems/bae97f66-6a9c-4cac-8662-658868f27295
-- title:
--   Eq. (4): $2h_\pm$ solve $\Delta(\Delta-d)=m^2R^2$ and $2h_+-2h_-=2\nu$
-- statement:
--   For every $d\in\mathbb N$ and $m,R\in\mathbb R$, with $\nu=\tfrac12\sqrt{d^2+4m^2R^2}$ and $2h_\pm=\tfrac d2\pm\nu$,
--   $$2h_+(2h_+-d)=m^2R^2,\qquad 2h_-(2h_--d)=m^2R^2,\qquad 2h_+-2h_-=2\nu .$$
--
--   These are the two boundary exponents of the radial equation at $r=\pi/2$: $(\cos r)^{2h_+}$ is the decay of normalizable modes (eq. 6) and $(\cos r)^{2h_-}$ the growth of non-normalizable ones (eq. 9).
-- source:
--   S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eq. (4), p. 2707

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology

namespace Giddings1999

/-- **Milestone, eq. (4)**: `2h₊` and `2h₋` are the two roots of `Δ(Δ − d) = m²R²`, and they differ
by `2ν`. -/
theorem twoH_indicial_roots (d : ℕ) (m R : ℝ) :
    twoHPlus d m R * (twoHPlus d m R - d) = m ^ 2 * R ^ 2 ∧
    twoHMinus d m R * (twoHMinus d m R - d) = m ^ 2 * R ^ 2 ∧
    twoHPlus d m R - twoHMinus d m R = 2 * nu d m R := by
  sorry

end Giddings1999
