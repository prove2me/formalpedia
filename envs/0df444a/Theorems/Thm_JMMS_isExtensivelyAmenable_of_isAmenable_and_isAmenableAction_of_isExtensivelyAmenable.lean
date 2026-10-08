-- Prove2me | Theorems.Thm_JMMS_isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
-- name    : JMMS.isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:21:43.231978+00:00
-- url     : https://prove2.me/theorems/0289f0fb-8514-44dd-9690-d5f90564c37d
-- title:
--   Lemma 2.1 — actions of amenable groups are extensively amenable, and extensively amenable actions are amenable
-- statement:
--   For every action of a group $G$ on a set $X$: if $G$ is amenable then the action is extensively amenable; and if $X$ is nonempty and the action is extensively amenable then it is amenable, that is, $X$ carries a $G$-invariant mean.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 6: “Lemma 2.1. Every action of an amenable group is extensively amenable, and every extensively amenable action on a nonempty set is amenable.”
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 6, Lemma 2.1

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange
open scoped ENNReal

namespace JMMS

theorem isExtensivelyAmenable_of_isAmenable_and_isAmenableAction_of_isExtensivelyAmenable
    {G X : Type*} [Group G] [MulAction G X] :
    (Garrido.IsAmenable G → IsExtensivelyAmenable G X) ∧
      (Nonempty X → IsExtensivelyAmenable G X → IsAmenableAction G X) := by
  sorry

end JMMS
