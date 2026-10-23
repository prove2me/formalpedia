-- Prove2me | Theorems.Thm_NonstatRL_PerStep_proposition2_per_step_regret
-- name    : NonstatRL.PerStep.proposition2_per_step_regret
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:33.411573+00:00
-- url     : https://prove2.me/theorems/32bedd26-d1a0-4d4d-aa83-6170be0d4b6b
-- title:
--   Proposition 2 — per-step dynamic regret of SWUCRL2-CW
-- statement:
--   Consider an episode of the paper's nonstationary finite MDP algorithm. Each state has a nonempty finite allowed action set, $S>1$, $0<\delta<1$, and widening $\eta\ge0$. At the episode start, the local reward and transition estimation-error events hold. The EVI output satisfies its optimistic and near-optimality contract. A transition model with diameter at most $D$ has every allowed row in the widened episode-start transition confidence region. For any round $t$ after that start and before the horizon on which the policy chooses $a_t=\tilde\pi_{\tau(m)}(s_t)$,
--
--   $$
--   \begin{aligned}
--   \rho_t^*-r_t(s_t,a_t)\le{}&\sum_{s'}p_t(s'\mid s_t,a_t)\tilde\gamma_{\tau(m)}(s')-\tilde\gamma_{\tau(m)}(s_t)+\frac1{\sqrt{\tau(m)}}\\
--   &+2\operatorname{var}_{r,t}+4D(\operatorname{var}_{p,t}+\eta)\\
--   &+2\operatorname{rad}_{r,\tau(m)}(s_t,a_t)+4D\operatorname{rad}_{p,\tau(m)}(s_t,a_t).
--   \end{aligned}
--   $$
--
--   This is the explicit per-round engine of the paper's regret analysis. **Formalization Note** The printed free pair in the last radius is read as $(s_t,a_t)$, as in the proof. The end of the episode is unnecessary once the policy-action relation is given. Time indices in Lean are zero-based, so the displayed one-based $\tau(m)$ is represented by $\tau_m+1$. The events are assumed only at the episode start, where they are used.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 14, Proposition 2; proof pp. 38–41

import Mathlib
import Definitions.Def_NonstatRL_PerStep_EVIOutput

open BanditAlgorithm ENNReal

namespace NonstatRL.PerStep

theorem proposition2_per_step_regret {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (η : ℝ) (hη : 0 ≤ η)
    (W : ℕ) (st : ℕ → Fin S) (ac : ℕ → Fin A) (R : ℕ → ℝ)
    (τm t : ℕ) (ht : τm ≤ t ∧ t < T)
    (heR : EventR M As T δ st ac R (τm - W) τm)
    (heP : EventP M As T δ st ac (τm - W) τm)
    (πt : Fin S → Fin A) (rt : Fin S → Fin A → ℝ)
    (pt : Fin S → Fin A → Fin S → ℝ) (ρt : ℝ) (γt : Fin S → ℝ)
    (hevi : IsEVIOutput As T δ η W τm st ac R πt rt pt ρt γt)
    (D : ℝ) (Mw : FiniteMDP S A)
    (hw : ∀ s a, a ∈ As s →
      (fun s' => (Mw.P s a s' : ℝ)) ∈
        Hp As T δ st ac (τm - W) τm η s a)
    (hdiam : NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal D)
    (hact : ac t = πt (st t)) :
    NonstatRL.Oracle.optGain (M t) As - (M t).r (st t) (ac t) ≤
      (∑ s' : Fin S, ((M t).P (st t) (ac t) s' : ℝ) * γt s') -
      γt (st t) + 1 / Real.sqrt (τm + 1) +
      (2 * varR M As (τm - W) t +
        4 * D * (varP M As (τm - W) t + η)) +
      (2 * radR As T δ
        (countPlus st ac (τm - W) τm (st t) (ac t)) +
        4 * D * radP As T δ
          (countPlus st ac (τm - W) τm (st t) (ac t))) := by sorry

end NonstatRL.PerStep
