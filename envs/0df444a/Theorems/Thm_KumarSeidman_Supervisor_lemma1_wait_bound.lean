-- Prove2me | Theorems.Thm_KumarSeidman_Supervisor_lemma1_wait_bound
-- name    : KumarSeidman.Supervisor.lemma1_wait_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:23.89042+00:00
-- url     : https://prove2.me/theorems/b6255299-b116-4a36-8758-e345dbe3ae4f
-- title:
--   Lemma 1 1): a queued buffer completes its next run within $\gamma_m-\zeta_m$
-- statement:
--   Consider a system satisfying the capacity condition (1), supervisor parameters $\gamma$ satisfying (24) and thresholds $z\ge 0$, and a supervised trajectory. Let $b_{p,i}$ be a buffer of machine $m=\mu_{p,i}$ that enters the priority queue $Q_m$ at time $t_{\mathrm{in}}$. Then its subsequent processing run exists, and the time $t_{\mathrm{complete}}$ at which it is completed satisfies
--   $$
--   t_{\mathrm{complete}}-t_{\mathrm{in}}\le \gamma_m-\zeta_m,\qquad \zeta_m=\gamma_m(1-\rho_m)-\sum_{b\in B_m}\max_{b'\in B_m}\delta_{b',b}.
--   $$
--
--   This is the basic waiting-time guarantee of the supervisor: once a buffer is queued, the machine must reach it within a bounded time, whatever the underlying policy does.
--
--   **Formalization Note** As on the page, $t_{\mathrm{in}}$ is an instant at which $b_{p,i}$ enters $Q_m$ (Lean `EntersQ`: it is in $Q_m$ at $t_{\mathrm{in}}$, and $t_{\mathrm{in}}=0$ or it was not waiting in $Q_m$ just before). $Q_m$ is not a separate state: a buffer is in $Q_m$ exactly when the machine's current run is not on it and its level exceeds $z_{p,i}$. Existence of the subsequent run is part of the conclusion.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 296, Lemma 1 1), (25)–(26)

import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Lemma 1 1) (Kumar–Seidman 1990, p. 296, (25)–(26)). If buffer `b` enters the priority
queue `Q_m` (`m = μ_b`) at time `t_in`, then its subsequent processing run exists and is
completed by `t_in + γ_m − ζ_m`. -/
theorem lemma1_wait_bound {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn : ℝ)
    (hin : T.EntersQ z b tIn) :
    ∃ k : ℕ, T.IsNextRun b tIn k ∧ T.HasNext (S.mach b) k ∧
      T.s (S.mach b) (k + 1) - tIn ≤ γ (S.mach b) - zeta S γ (S.mach b) := by sorry

end KumarSeidman.Supervisor
