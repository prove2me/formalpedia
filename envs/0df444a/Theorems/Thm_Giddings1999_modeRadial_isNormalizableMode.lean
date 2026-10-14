-- Prove2me | Theorems.Thm_Giddings1999_modeRadial_isNormalizableMode
-- name    : Giddings1999.modeRadial_isNormalizableMode
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T01:50:22.908463+00:00
-- url     : https://prove2.me/theorems/b6acac0f-a7ab-42cc-af08-8b8902b38384
-- title:
--   Eq. (5): $\chi_{nl}$ is a normalizable mode at frequency $\omega_{nl}$
-- statement:
--   Let $d\ge2$, $R>0$, $m\in\mathbb R$ and $n,l\in\mathbb N$. The profile $\chi_{nl}$ is a normalizable mode with angular momentum $l$ and frequency $\omega_{nl}=2h_++2n+l$: it solves the radial equation, is not identically zero on $(0,\pi/2)$, is bounded near $r=0$, and satisfies
--   $$\int_0^{\pi/2}\tan^{d-1}r\;\chi_{nl}(r)^2\,dr<\infty .$$
--
--   This is the "if" direction of the goal theorem.
-- source:
--   S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eq. (5), p. 2707

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology

namespace Giddings1999

/-- **Milestone, eq. (5)**: each `χ_{nl}` is a normalizable mode at frequency `ω_{nl}`. -/
theorem modeRadial_isNormalizableMode (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R) (n l : ℕ) :
    IsNormalizableMode d m R (omegaNL d m R n l) l (modeRadial d m R n l) := by
  sorry

end Giddings1999
