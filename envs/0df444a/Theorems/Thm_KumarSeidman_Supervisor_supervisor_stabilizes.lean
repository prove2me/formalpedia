-- Prove2me | Theorems.Thm_KumarSeidman_Supervisor_supervisor_stabilizes
-- name    : KumarSeidman.Supervisor.supervisor_stabilizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:34.327479+00:00
-- url     : https://prove2.me/theorems/65a9d7bd-d2c5-4651-8baa-677ff575c588
-- title:
--   Theorem 2: the run-truncating FCFS supervisor keeps every buffer bounded under $\rho_m<1$
-- statement:
--   Consider any manufacturing system with set-up times that satisfies the capacity condition
--   $$
--   \rho_m=\sum_{(p,i):\,\mu_{p,i}=m}d_p\tau_{p,i}<1\qquad(1\le m\le M).
--   $$
--   Choose supervisor parameters $\gamma_m$ with $\gamma_m(1-\rho_m)>\sum_{b\in B_m}\max_{b'\in B_m}\delta_{b',b}$ (24) and thresholds $z_{p,i}\ge 0$. Apply the supervisor (truncation of runs at $\gamma_m d_p\tau_{p,i}$, an FCFS priority queue $Q_m$ of buffers whose level exceeds $z_{p,i}$, and processing of each queued buffer for exactly $\gamma_m d_p\tau_{p,i}$ unless it clears) at every machine, on top of an arbitrary scheduling policy. Then every trajectory, from every initial state (initial levels, initial set-ups and initial queue order), has all buffer levels bounded over all time:
--   $$
--   \sup_{0\le t<\infty}x_{p,i}(t)<+\infty\qquad\text{for all }p,i .
--   $$
--
--   The capacity condition is necessary for stability of any policy. The paper shows in §III that natural distributed policies (clearing policies) can be unstable even when it holds; this theorem shows that a simple distributed supervisor makes every policy stable whenever it holds.
--
--   **Formalization Note** The bound may depend on the trajectory. The base policy is constrained only by the run structure of the model (contiguous runs, no idling outside runs, full processing rate on a nonempty buffer) and by the supervisor's rules; it need not be a clearing policy.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 297, Theorem 2

import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Theorem 2 (Kumar–Seidman 1990, p. 297). Under the capacity condition (1), with run-length
parameters `γ` satisfying (24) and arbitrary thresholds `z ≥ 0`, every trajectory of an
arbitrary scheduling policy modified by the supervisor at all machines keeps every buffer level
bounded over `[0, ∞)`, from every initial state. -/
theorem supervisor_stabilizes {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) :
    T.IsStable := by sorry

end KumarSeidman.Supervisor
