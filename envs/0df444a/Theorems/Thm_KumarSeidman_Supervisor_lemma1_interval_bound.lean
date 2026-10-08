-- Prove2me | Theorems.Thm_KumarSeidman_Supervisor_lemma1_interval_bound
-- name    : KumarSeidman.Supervisor.lemma1_interval_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:46.897783+00:00
-- url     : https://prove2.me/theorems/7a6b534f-4755-4743-8fc8-5bf167a946d9
-- title:
--   Lemma 1 4): a buffer stays above $g_{p,i}$ for at most $a_{p,i}+c_{p,i}\beta_{p,i}(t)$
-- statement:
--   Under (1), (24) and $z\ge 0$, let a supervised trajectory be given and let $b_{p,i}$ be a buffer of machine $m=\mu_{p,i}$. Put
--   $$
--   g_{p,i}:=\max(\gamma_m d_p,z_{p,i})+\gamma_m d_p,\quad a_{p,i}:=\Bigl(2+\frac{\gamma_m-\zeta_m}{\zeta_m}\Bigr)(\gamma_m-\zeta_m),\quad c_{p,i}:=\frac{\gamma_m-\zeta_m}{\zeta_m d_p\tau_{p,i}} .
--   $$
--   If $[t,t']$ is any interval with $t\ge 0$ such that $x_{p,i}(\sigma)\ge g_{p,i}$ for all $\sigma\in[t,t']$, then
--   $$
--   t'-t\le a_{p,i}+c_{p,i}\,\beta_{p,i}(t).
--   $$
--
--   This is the form of Lemma 1 used in the proof of Theorem 2: excursions of a buffer above $g_{p,i}$ have a length bounded in terms of the backlog at their start, which the induction along the route of part type $p$ keeps bounded.
--
--   **Formalization Note** The printed $c_{p,i}:=((\gamma_m-\zeta_m)/\zeta_m d_p\tau_{p,i})$ is read as $(\gamma_m-\zeta_m)/(\zeta_m d_p\tau_{p,i})$, as the proof's display (28) shows.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 296, Lemma 1 4)

import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism

namespace KumarSeidman.Supervisor

/-- Lemma 1 4) (Kumar–Seidman 1990, p. 296, right column). If `x_{p,i}(σ) ≥ g_{p,i}` throughout `[t, t']`,
where `g_{p,i} = max(γ_m d_p, z_{p,i}) + γ_m d_p`, then `t' − t ≤ a_{p,i} + c_{p,i} β_{p,i}(t)`
with `a_{p,i} = (2 + (γ_m − ζ_m)/ζ_m)(γ_m − ζ_m)` and
`c_{p,i} = (γ_m − ζ_m)/(ζ_m d_p τ_{p,i})`. -/
theorem lemma1_interval_bound {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (t t' : ℝ) (ht : 0 ≤ t)
    (hx : ∀ σ ∈ Set.Icc t t',
      max (γ (S.mach b) * S.d b.1) (z b) + γ (S.mach b) * S.d b.1 ≤ T.x b σ) :
    t' - t ≤
      (2 + (γ (S.mach b) - zeta S γ (S.mach b)) / zeta S γ (S.mach b)) *
          (γ (S.mach b) - zeta S γ (S.mach b)) +
        (γ (S.mach b) - zeta S γ (S.mach b)) /
            (zeta S γ (S.mach b) * S.d b.1 * S.tau b) * backlog T b t := by sorry

end KumarSeidman.Supervisor
