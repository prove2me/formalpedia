-- Prove2me | Theorems.Thm_KumarSeidman_CAF_caf_policies_stable
-- name    : KumarSeidman.CAF.caf_policies_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:42.800983+00:00
-- url     : https://prove2.me/theorems/49958925-33b2-4a0b-938a-d1ab5f605bf3
-- title:
--   Theorem 1 (Kumar–Seidman): if ρ′ₘ < 1 for every machine, all CAF policies are stable for all initial conditions
-- statement:
--   Consider a manufacturing system with $P$ part types and $M$ machines, routes $\mu_{p,1},\dots,\mu_{p,n_p}$ (revisits allowed), input rates $d_p>0$, processing times $\tau_{p,i}>0$ and set-up times $\delta_{b,b'}\ge0$. For each buffer $b_{p,i}$ let $\lambda_{p,i}$, the prior machine $\pi_{p,i}$ and the modified input rate $d'_{p,i}$ be defined by (11)–(13): $d'_{p,i}=1/\tau_{p,\lambda_{p,i}}$ if the prior machine exists and is diconnected with $\mu_{p,i}$, and $d'_{p,i}=d_p$ otherwise. If the more stringent capacity condition
--
--   $$
--   \rho'_m:=\sum_{(p,i):\,\mu_{p,i}=m}d'_{p,i}\,\tau_{p,i}<1\qquad\text{for all } m \tag{14}
--   $$
--
--   holds, then all CAF policies are stable for all system initial conditions: for all constants $\varepsilon_m>0$ and $K_m$, every fluid trajectory, from any initial levels and initial set-ups, that obeys the clearing rule (Definition 1) and the clear-a-fraction rule (2) with these constants satisfies
--
--   $$
--   \sup_{0\le t<\infty}x_{p,i}(t)<+\infty\qquad\text{for every buffer } b_{p,i}.
--   $$
--
--   Theorem 1 contrasts with the examples of §III, in which clearing policies are unstable although the usual capacity condition $\rho_m<1$ holds: on machines that lie in a common cycle of material flow, (14) budgets for the peak rate at which an upstream machine can release parts, not only for the average rate $d_p$.
--
--   **Formalization Note** The model, the reading of "nonempty" in Definition 1 as "nonempty or with inflow starting now", and the run structure are those of the imported definition files. The bound on each buffer may depend on the trajectory (and so on the initial state); no bound uniform in the initial state is claimed. Condition (1) is not assumed separately: (14) implies it, since $d'_{p,i}\ge d_p$. Set-up times may be zero.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 294, Theorem 1, (11)–(14)

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy

namespace KumarSeidman.CAF

/-- **Theorem 1** (Kumar–Seidman 1990, p. 294). If the more stringent capacity condition (14),
`ρ'_m < 1` for every machine `m`, holds, then all CAF policies are stable for all system
initial conditions: for all CAF constants `ε_m > 0`, `K_m`, and every trajectory from any
initial state obeying the clearing and clear-a-fraction rules with these constants, every
buffer level is bounded on `[0, ∞)`. -/
theorem caf_policies_stable {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (ε K : Fin M → ℝ) (T : Trajectory S) (hT : T.IsCAF ε K) : T.IsStable := by sorry

end KumarSeidman.CAF
