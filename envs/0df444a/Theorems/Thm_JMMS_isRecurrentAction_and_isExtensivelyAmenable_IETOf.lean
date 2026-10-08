-- Prove2me | Theorems.Thm_JMMS_isRecurrentAction_and_isExtensivelyAmenable_IETOf
-- name    : JMMS.isRecurrentAction_and_isExtensivelyAmenable_IETOf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:27:45.182777+00:00
-- url     : https://prove2.me/theorems/4355cc67-bba5-47b3-a196-73bc6e82a4bf
-- title:
--   Lemma 5.2 — for Λ of rational rank at most 2, IET(Λ) ↷ ℝ/ℤ is recurrent and extensively amenable
-- statement:
--   Let $\Lambda$ be a finitely generated subgroup of $\mathbf R/\mathbf Z$ of rational rank at most $2$. Then the action of $\mathrm{IET}(\Lambda)$ on $\mathbf R/\mathbf Z$ is recurrent (for every symmetric, finitely supported probability measure $\mu$ on $\mathrm{IET}(\Lambda)$ and every starting point $x_0$, the induced random walk returns to $x_0$ with probability $1$) and extensively amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 17: “Lemma 5.2. If $\mathrm{rk}_{\mathbf Q}(\Lambda) \le 2$, the action of $\mathrm{IET}(\Lambda)$ on $\mathbf R/\mathbf Z$ is recurrent. In particular, it is extensively amenable.” The standing assumption of §5.1 (p. 16) is “Let $\Lambda < \mathbf R/\mathbf Z$ be a finitely generated subgroup of the circle.”
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 17, Lemma 5.2

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

theorem isRecurrentAction_and_isExtensivelyAmenable_IETOf (Λ : AddSubgroup UnitAddCircle)
    (hΛ : Λ.FG) (hrk : rationalRank Λ ≤ 2) :
    IsRecurrentAction ↥(IETOf Λ) UnitAddCircle ∧
      IsExtensivelyAmenable ↥(IETOf Λ) UnitAddCircle := by
  sorry

end JMMS
