-- Prove2me | Theorems.Thm_JMMS_isExtensivelyAmenable_of_isRecurrentAction
-- name    : JMMS.isExtensivelyAmenable_of_isRecurrentAction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:26:30.616614+00:00
-- url     : https://prove2.me/theorems/373033a4-9dc2-4b13-8172-dd50b31415cd
-- title:
--   Theorem 4.2 — recurrent actions are extensively amenable
-- statement:
--   Let a group $G$ act on a set $X$. If the action is recurrent — for every symmetric, finitely supported probability measure $\mu$ on $G$ and every $x_0 \in X$, the random walk on $X$ started at $x_0$, which moves from $x$ to $g x$ with probability $\mu(g)$, returns to $x_0$ with probability $1$ — then the action is extensively amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 16: “Theorem 4.2 (Theorem 1.2 in [JNdlS13]). Recurrent actions are extensively amenable.”
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 16, Theorem 4.2

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

theorem isExtensivelyAmenable_of_isRecurrentAction {G X : Type*} [Group G] [MulAction G X]
    (h : IsRecurrentAction G X) : IsExtensivelyAmenable G X := by
  sorry

end JMMS
