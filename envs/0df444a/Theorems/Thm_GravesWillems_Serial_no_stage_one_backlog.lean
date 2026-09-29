-- Prove2me | Theorems.Thm_GravesWillems_Serial_no_stage_one_backlog
-- name    : GravesWillems.Serial.no_stage_one_backlog
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:18:16.408934+00:00
-- url     : https://prove2.me/theorems/95cb41c0-c852-4afe-b000-5ca9e91fb8b0
-- title:
--   Eq. (A3) — the service constraints guarantee no backlog at stage 1
-- statement:
--   Consider the $N$-stage serial base-stock system with lead times $T_i \in \mathbb{N}$ and real base stocks $B_i$, and let $D : \mathbb{N} \to \mathbb{R}$ be a demand bound for the demand path $d$, i.e.
--   $$d(a, a + s] \le D(s) \qquad \text{for every } a \in \mathbb{Z},\ s \in \mathbb{N}.$$
--   If the base stocks satisfy the constraints (A3),
--   $$B_1 + B_2 + \dots + B_i \ge D(T_1 + T_2 + \dots + T_i), \qquad i = 1, \dots, N,$$
--   then stage $1$ never has a backlog: $Q_1(t) = 0$ for every period $t$.
--
--   This is why 100% service to the external customer can be imposed through the linear constraints (A3), and why $E[Q_1]$ drops out of the objective of $\mathbf P^*$.
--
--   **Formalization Note** Only the sufficiency direction is stated. The page adds that, when the demand bounds can be realized, (A3) is also necessary; that direction is not part of this item.
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, p. 81, Appendix, Eq. (A3)

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP

namespace GravesWillems.Serial

/-- Eq. (A3) of Graves–Willems 2000 (Appendix, p. 81), sufficiency: if the demand path never
exceeds the demand bound, `d(a, a + s] ≤ D(s)` for every time `a` and every number of periods `s`,
and the base stocks satisfy the constraints (A3), then stage 1 never has a backlog:
`Q₁(t) = 0` for all `t`. -/
theorem no_stage_one_backlog (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) (d : ℤ → ℝ)
    (hdD : ∀ (a : ℤ) (s : ℕ), windowDemand d a (a + (s : ℤ)) ≤ D s)
    (hB : ServiceConstraints N T D B) (t : ℤ) :
    backlog N T B d 1 t = 0 := by sorry

end GravesWillems.Serial
