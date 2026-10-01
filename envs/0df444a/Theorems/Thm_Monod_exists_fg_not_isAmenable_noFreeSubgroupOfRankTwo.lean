-- Prove2me | Theorems.Thm_Monod_exists_fg_not_isAmenable_noFreeSubgroupOfRankTwo
-- name    : Monod.exists_fg_not_isAmenable_noFreeSubgroupOfRankTwo
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T13:21:48.023987+00:00
-- url     : https://prove2.me/theorems/ad979dd8-badd-4141-84e8-0d07fe8f2570
-- title:
--   Corollary 3 — for A ≠ ℤ, H(A) has finitely generated non-amenable subgroups without free subgroups
-- statement:
--   If $A \neq \mathbf{Z}$, then $H(A)$ has a finitely generated subgroup that is not amenable and has no free subgroup of rank two.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 1, Corollary 3

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Classes
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem exists_fg_not_isAmenable_noFreeSubgroupOfRankTwo {A : Subring ℝ} (hA : A ≠ ⊥) :
    ∃ K : Subgroup (H A), K.FG ∧ ¬ Garrido.IsAmenable K ∧ Chou.NoFreeSubgroupOfRankTwo K := by
  sorry

end Monod
