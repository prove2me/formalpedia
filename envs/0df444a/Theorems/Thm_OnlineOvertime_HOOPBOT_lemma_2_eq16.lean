-- Prove2me | Theorems.Thm_OnlineOvertime_HOOPBOT_lemma_2_eq16
-- name    : OnlineOvertime.HOOPBOT.lemma_2_eq16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:53.225919+00:00
-- url     : https://prove2.me/theorems/74ba0657-c307-42f7-b4fe-0a0f207b10ed
-- title:
--   Lemma 2, statement (16), p. 21 — with θ1 = θ2 = θ∗, overrunning B + U prices customer K2 out
-- statement:
--   Let an instance satisfy the standing assumptions and run Algorithm 1 (HOOP-BOT) with $\theta_1=\theta_2=\theta^*$, the balancing point (11), and any tie-break for the argmax of Step 3. Fix a server-date $(i,t)$ and a customer $K_2$ allocated to $(i,t)$. Let $x^{(K_2)}_{i,t}$ be the regular-capacity price of $(i,t)$ after iteration $K_2$, and $y$ the assignment after iteration $K_2$. If
--   $$\sum_{j\le K_2}b_{i,j}\,y_{i,j,t}>B_{i,t}+U_{i,t},\qquad\text{then}\qquad c_{i,K_2}-b_{i,K_2}\,x^{(K_2)}_{i,t}<0 .$$
--
--   So at the iteration where both the regular capacity and the overtime budget of $(i,t)$ are used up, the updated price is high enough that customer $K_2$ would no longer be accepted at $(i,t)$; this is what makes the primal solution almost feasible.
--
--   **Formalization Note** The run is the step-by-step run of Algorithm 1 as defined in the model file, with $u_{i,t}=1$ initially as printed. The lemma's further clause that (13) and (14) also hold at $\theta_1=\theta^*$ is not part of this statement.
-- source:
--   Keyvanshokooh, Shi, Van Oyen, Online Advance Scheduling with Overtime: A Primal-Dual Approach, accepted manuscript (MSOM, accepted May 2019; SSRN 3352166), p. 21, Lemma 2, statement (16)

import Mathlib
import Definitions.Def_OnlineOvertime_HOOPBOT_Model

namespace OnlineOvertime.HOOPBOT

/-- Lemma 2, statement (16), p. 21. Run Algorithm 1 with `θ1 = θ2 = θ∗` of (11) and any argmax
tie-break. If customer `K₂` is allocated to server-date `(i, t)` and, after iteration `K₂`,
the service time allocated to `(i, t)` exceeds `B_{i,t} + U_{i,t}`, then the price
`x^{(K₂)}_{i,t}` after iteration `K₂` satisfies `c_{i,K₂} − b_{i,K₂} x^{(K₂)}_{i,t} < 0`. -/
theorem lemma_2_eq16 {n T m : ℕ} (I : Instance n T m) (hS : I.Standing)
    (sel : (Fin n × Fin T → ℝ) → Fin n × Fin T) (hsel : IsArgmaxSelector sel)
    (i : Fin n) (t : Fin T) (K₂ : Fin m) :
    let s := runPrefix I (thetaStar I) (thetaStar I) sel (K₂.val + 1)
    s.y K₂ i t = 1 → I.B i t + I.U i t < ∑ j, I.b j i * s.y j i t →
      I.c K₂ i - I.b K₂ i * s.x i t < 0 := by sorry

end OnlineOvertime.HOOPBOT
