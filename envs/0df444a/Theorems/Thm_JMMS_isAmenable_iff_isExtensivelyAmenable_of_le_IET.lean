-- Prove2me | Theorems.Thm_JMMS_isAmenable_iff_isExtensivelyAmenable_of_le_IET
-- name    : JMMS.isAmenable_iff_isExtensivelyAmenable_of_le_IET
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:23:59.426346+00:00
-- url     : https://prove2.me/theorems/8ddf9561-7ad4-4abb-b37a-c217c7cf5b31
-- title:
--   Proposition 5.3 — a subgroup of IET is amenable if and only if its action on ℝ/ℤ is extensively amenable
-- statement:
--   For every subgroup $G$ of $\mathrm{IET}$: $G$ is amenable if and only if the action of $G$ on $\mathbf R/\mathbf Z$ by evaluation is extensively amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 17: “Proposition 5.3. A subgroup $G \le \mathrm{IET}$ is amenable if and only if the action $G \curvearrowright \mathbf R/\mathbf Z$ is extensively amenable.”
--
--   Applied to $G = \mathrm{IET}$, it makes the goal equivalent to extensive amenability of the action of $\mathrm{IET}$ on the circle.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 17, Proposition 5.3

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

theorem isAmenable_iff_isExtensivelyAmenable_of_le_IET (G : Subgroup (Equiv.Perm UnitAddCircle))
    (hG : G ≤ IET) :
    Garrido.IsAmenable ↥G ↔ IsExtensivelyAmenable ↥G UnitAddCircle := by
  sorry

end JMMS
