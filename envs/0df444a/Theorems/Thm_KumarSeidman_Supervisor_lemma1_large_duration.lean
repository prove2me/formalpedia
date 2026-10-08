-- Prove2me | Theorems.Thm_KumarSeidman_Supervisor_lemma1_large_duration
-- name    : KumarSeidman.Supervisor.lemma1_large_duration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:27.695952+00:00
-- url     : https://prove2.me/theorems/c3651c40-540b-435e-b792-865299ee380c
-- title:
--   Lemma 1 3): how long a buffer can stay above $\max(\gamma_m d_p, z_{p,i})$ after entering $Q_m$
-- statement:
--   Under (1), (24) and $z\ge 0$, let a supervised trajectory be given and let buffer $b_{p,i}$ of machine $m=\mu_{p,i}$ enter $Q_m$ at time $t_{\mathrm{in}}$. Suppose that $t'$ is such that
--   $$
--   x_{p,i}(\sigma)\ge\max(\gamma_m d_p,z_{p,i})\ \text{ for all }\sigma\in[t_{\mathrm{in}},t'],\qquad x_{p,i}(\sigma)>z_{p,i}\ \text{ for all }\sigma\in(t_{\mathrm{in}},t'] .
--   $$
--   Then
--   $$
--   t'-t_{\mathrm{in}}\le\Bigl(1+\frac{\beta_{p,i}(t_{\mathrm{in}})}{\zeta_m d_p\tau_{p,i}}\Bigr)(\gamma_m-\zeta_m).
--   $$
--
--   A buffer cannot stay large for longer than a time proportional to its backlog: every time it is served it re-enters the queue, and each service lowers the backlog by a fixed amount.
--
--   **Formalization Note** The paper's hypothesis is $x_{p,i}(\sigma)\ge\max(\gamma_m d_p,z_{p,i})$ on $[t_{\mathrm{in}},t']$. Its proof needs $b_{p,i}$ to re-enter $Q_m$ at each completion, and the Rule for Entering $Q_m$ requires the level to *exceed* $z_{p,i}$; with the printed hypothesis alone the statement fails (the buffer can sit at exactly $z_{p,i}$, never re-queued, for as long as an upstream buffer with a large threshold is ignored). The hypothesis $x_{p,i}>z_{p,i}$ on $(t_{\mathrm{in}},t']$ is added; it holds wherever the paper applies the lemma (in part 4) the level is at least $g_{p,i}>z_{p,i}$).
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 296, Lemma 1 3) (hypothesis corrected: strict threshold after t_in)

import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Lemma 1 3) (Kumar–Seidman 1990, p. 296), with the strict threshold needed for re-entry.
If `b = b_{p,i}` enters `Q_m` at `t_in`, `x_{p,i}(σ) ≥ max(γ_m d_p, z_{p,i})` on
`[t_in, t']` and `x_{p,i}(σ) > z_{p,i}` on `(t_in, t']`, then
`t' − t_in ≤ (1 + β_{p,i}(t_in)/(ζ_m d_p τ_{p,i}))(γ_m − ζ_m)`. -/
theorem lemma1_large_duration {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn t' : ℝ)
    (hin : T.EntersQ z b tIn)
    (hge : ∀ σ ∈ Set.Icc tIn t', max (γ (S.mach b) * S.d b.1) (z b) ≤ T.x b σ)
    (hgt : ∀ σ ∈ Set.Ioc tIn t', z b < T.x b σ) :
    t' - tIn ≤
      (1 + backlog T b tIn / (zeta S γ (S.mach b) * S.d b.1 * S.tau b)) *
        (γ (S.mach b) - zeta S γ (S.mach b)) := by sorry

end KumarSeidman.Supervisor
