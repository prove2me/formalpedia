-- Prove2me | Theorems.Thm_GrapheneTightBinding_Delta_diracK_eq_zero_and_Delta_diracKp_eq_zero
-- name    : GrapheneTightBinding.Delta_diracK_eq_zero_and_Delta_diracKp_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T20:44:14.211708+00:00
-- url     : https://prove2.me/theorems/ec2adf6c-0af5-4d53-ac6f-812850c897c6
-- title:
--   The Dirac points: $\Delta_K=\Delta_{K'}=0$
-- statement:
--   **The bands touch at the Dirac points.** For every $a>0$ the structure factor vanishes at
--   both corners of the Brillouin zone,
--   $$\Delta_K=0,\qquad \Delta_{K'}=0,
--   \qquad K=\frac{2\pi}{3\sqrt3a}(\sqrt3,1),\quad K'=\frac{2\pi}{3\sqrt3a}(\sqrt3,-1).$$
--   Since $E_\pm(k)=\pm t|\Delta_k|$, the two bands meet at zero energy at $K$ and $K'$: these
--   are the gapless points of the spectrum around which the low-energy physics of graphene is
--   organised.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem Delta_diracK_eq_zero_and_Delta_diracKp_eq_zero (a : ℝ) (ha : 0 < a) :
    Delta a (diracK a) = 0 ∧ Delta a (diracKp a) = 0 := by
  sorry

end GrapheneTightBinding
