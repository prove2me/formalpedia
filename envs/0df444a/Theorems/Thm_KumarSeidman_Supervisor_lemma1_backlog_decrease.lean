-- Prove2me | Theorems.Thm_KumarSeidman_Supervisor_lemma1_backlog_decrease
-- name    : KumarSeidman.Supervisor.lemma1_backlog_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:24.995796+00:00
-- url     : https://prove2.me/theorems/252d85eb-26f9-465d-b4b2-4c7e6f13b017
-- title:
--   Lemma 1 2): a full queued run lowers the backlog $\beta_{p,i}$ by $\zeta_m d_p\tau_{p,i}$
-- statement:
--   Under (1), (24) and $z\ge 0$, let a supervised trajectory be given, and suppose buffer $b_{p,i}$ of machine $m=\mu_{p,i}$ enters $Q_m$ at time $t_{\mathrm{in}}$ and its subsequent processing run is completed at $t_{\mathrm{complete}}$. With the backlog $\beta_{p,i}(t)=\sum_{j=1}^{i}\tau_{p,i}x_{p,j}(t)$,
--   $$
--   x_{p,i}(t_{\mathrm{in}})\ge \gamma_m d_p\ \Longrightarrow\ \beta_{p,i}(t_{\mathrm{complete}})\le \beta_{p,i}(t_{\mathrm{in}})-\zeta_m d_p\tau_{p,i}.
--   $$
--
--   The backlog is the Lyapunov-type quantity of the stability proof: each service of a large queued buffer removes a fixed amount of it.
--
--   **Formalization Note** The subsequent run is the first run on $b_{p,i}$ that starts at or after $t_{\mathrm{in}}$ and ends after it; its existence is Lemma 1 1). The weight $\tau_{p,i}$ multiplies every term of the backlog, as printed.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 296, Lemma 1 2)

import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Lemma 1 2) (Kumar–Seidman 1990, p. 296). If buffer `b = b_{p,i}` enters `Q_m` at
`t_in` with `x_{p,i}(t_in) ≥ γ_m d_p`, then at the completion `t_complete` of its subsequent
processing run the backlog has dropped by at least `ζ_m d_p τ_{p,i}`. -/
theorem lemma1_backlog_decrease {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn : ℝ)
    (hin : T.EntersQ z b tIn) (k : ℕ) (hk : T.IsNextRun b tIn k)
    (hnext : T.HasNext (S.mach b) k)
    (hlevel : γ (S.mach b) * S.d b.1 ≤ T.x b tIn) :
    backlog T b (T.s (S.mach b) (k + 1)) ≤
      backlog T b tIn - zeta S γ (S.mach b) * S.d b.1 * S.tau b := by sorry

end KumarSeidman.Supervisor
