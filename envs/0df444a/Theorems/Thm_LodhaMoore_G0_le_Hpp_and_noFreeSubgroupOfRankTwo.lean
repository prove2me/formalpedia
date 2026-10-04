-- Prove2me | Theorems.Thm_LodhaMoore_G0_le_Hpp_and_noFreeSubgroupOfRankTwo
-- name    : LodhaMoore.G0_le_Hpp_and_noFreeSubgroupOfRankTwo
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T19:14:17.4957+00:00
-- url     : https://prove2.me/theorems/b7adf630-6062-4c41-a224-f9595c7b43af
-- title:
--   §1 — G₀ lies in Monod's group H and has no nonabelian free subgroup
-- statement:
--   $G_0 = \langle a, b, c\rangle$ is a subgroup of Monod's group $H$ of piecewise projective homeomorphisms of the projective line fixing $\infty$ (`Monod.Hpp`), and $G_0$ has no subgroup that is free of rank two (`Chou.NoFreeSubgroupOfRankTwo`: no injective homomorphism from the free group on two generators).
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 2, §1

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_Chou_Classes

namespace LodhaMoore

theorem G0_le_Hpp_and_noFreeSubgroupOfRankTwo :
    G0 ≤ Monod.Hpp ∧ Chou.NoFreeSubgroupOfRankTwo G0 := by
  sorry

end LodhaMoore
