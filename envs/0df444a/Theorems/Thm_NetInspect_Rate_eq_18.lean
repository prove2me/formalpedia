-- Prove2me | Theorems.Thm_NetInspect_Rate_eq_18
-- name    : NetInspect.Rate.eq_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:19.469955+00:00
-- url     : https://prove2.me/theorems/ea24405a-7f4a-41b9-abeb-96ced086ff14
-- title:
--   (18), p. 17 (proved in step (i.b), p. ec13) — for b1 < n*, b2 < m*, the value is linear in b2: U*(b1,b2) = b2·U*(b1,1)
-- statement:
--   Let $\mathcal G$ be a detection model, $b_1<n^*$ and $1\le b_2<m^*$. Then the value of the game $\Gamma(b_1,b_2)$ is linear in the attack resources:
--   $$
--   U^*(b_1,b_2)=b_2\,U^*(b_1,1).
--   $$
--
--   The paper writes this as $U^*(b_1,b_2)=(1-r^*_{b_1})\,b_2$, where $r^*_{b_1}$ is the equilibrium detection rate of Theorem 2; since $U^*(b_1,1)=1-r^*_{b_1}$, the two forms agree. The linearity is what makes the equilibrium detection rate independent of $b_2$.
--
--   **Formalization Note** The statement is written with $U^*(b_1,1)$ in place of $1-r^*_{b_1}$, so that it does not refer forward to the number $r^*_{b_1}$ defined by Theorem 2. $U^*$ is the optimal value of (LP1). The hypothesis $b_2\ge 1$ is added, as for Theorem 1.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, p. 17, (18); p. ec13, proof of Theorem 2, step (i.b)

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- (18) (p. 17), proved in step (i.b) (p. ec13): for `b1 < n*` and `1 ≤ b2 < m*` the value
of the game is linear in `b2`, `U*(b1, b2) = b2 · U*(b1, 1)` (`U*(b1, 1) = 1 − r*_{b1}`). -/
theorem eq_18 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    G.gameValue b1 b2 = (b2 : ℝ) * G.gameValue b1 1 := by sorry

end NetInspect.Rate
