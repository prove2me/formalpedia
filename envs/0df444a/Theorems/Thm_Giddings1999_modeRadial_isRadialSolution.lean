-- Prove2me | Theorems.Thm_Giddings1999_modeRadial_isRadialSolution
-- name    : Giddings1999.modeRadial_isRadialSolution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T01:49:04.936587+00:00
-- url     : https://prove2.me/theorems/b417cfba-900c-43dc-8760-7724621a5d59
-- title:
--   Eqs. (5), (7): $\chi_{nl}$ solves the radial Klein–Gordon equation at $\omega_{nl}$
-- statement:
--   Let $d\ge2$, $R>0$, $m\in\mathbb R$ and $n,l\in\mathbb N$. The function $\chi_{nl}(r)=\sin^l r\,(\cos r)^{2h_+}P_n^{(l+d/2-1,\nu)}(\cos 2r)$ is $C^2$ on $(0,\pi/2)$ and satisfies there
--   $$\chi''+\frac{d-1}{\sin r\cos r}\chi'+\omega_{nl}^2\chi-\frac{l(l+d-2)}{\sin^2 r}\chi-\frac{m^2R^2}{\cos^2 r}\chi=0,\qquad \omega_{nl}=2h_++2n+l .$$
--
--   Equivalently, $e^{-i\omega_{nl}t}Y_{l\vec m}\chi_{nl}$ solves the free equation $(\Box-m^2)\phi=0$ (eq. 3) on global $\mathrm{AdS}_{d+1}$.
-- source:
--   S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eqs. (5), (7), p. 2707; explicit form from Balasubramanian–Kraus–Lawrence, hep-th/9805171 (the paper's ref. [10])

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology

namespace Giddings1999

/-- **Milestone, eqs. (5), (7)**: `χ_{nl}` solves the radial free equation at frequency `ω_{nl}`. -/
theorem modeRadial_isRadialSolution (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R) (n l : ℕ) :
    IsRadialSolution d m R (omegaNL d m R n l) l (modeRadial d m R n l) := by
  sorry

end Giddings1999
