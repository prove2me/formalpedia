-- Prove2me | Theorems.Thm_JMMS_isAmenable_IETOf_of_rationalRank_le_two
-- name    : JMMS.isAmenable_IETOf_of_rationalRank_le_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:28:46.727522+00:00
-- url     : https://prove2.me/theorems/39a5dbed-4a4a-4973-a82a-4e36bd81964d
-- title:
--   Theorem 5.1 — for finitely generated Λ of rational rank at most 2, IET(Λ) is amenable
-- statement:
--   Let $\Lambda$ be a finitely generated subgroup of $\mathbf R/\mathbf Z$ of rational rank at most $2$. Then $\mathrm{IET}(\Lambda)$, the group of interval exchange transformations all of whose angles lie in $\Lambda$, is amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 17: “Theorem 5.1. Let $\Lambda < \mathbf R/\mathbf Z$ be finitely generated. If $\mathrm{rk}_{\mathbf Q}(\Lambda) \le 2$, then $\mathrm{IET}(\Lambda)$ is amenable.”
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 17, Theorem 5.1

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

theorem isAmenable_IETOf_of_rationalRank_le_two (Λ : AddSubgroup UnitAddCircle) (hΛ : Λ.FG)
    (hrk : rationalRank Λ ≤ 2) : Garrido.IsAmenable ↥(IETOf Λ) := by
  sorry

end JMMS
