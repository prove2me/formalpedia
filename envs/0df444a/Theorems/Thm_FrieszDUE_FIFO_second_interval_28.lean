-- Prove2me | Theorems.Thm_FrieszDUE_FIFO_second_interval_28
-- name    : FrieszDUE.FIFO.second_interval_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:21:35.075243+00:00
-- url     : https://prove2.me/theorems/84ffd297-120c-4fe4-a18d-0b1731498eed
-- title:
--   (25)–(28), pp. 185–186 — on [t₁, t₂]: τ(t) = t + α∫_{τ₁⁻¹(t)}ᵗ u + β and τ′ = αu(t) + 1/(1 + αu[τ₁⁻¹(t)]) > αu(t)
-- statement:
--   Let $\alpha, \beta > 0$, let the entry rate $u$ be nonnegative and continuous on $[0, \infty)$, and let $\tau$ satisfy the exit-time equation $\tau(t) = t + \alpha x(t) + \beta$ for $t \ge 0$, with $x(t)$ the mass of the vehicles on the arc at time $t$. Let $t_1 = \tau(0)$ and $t_2 = \tau(t_1)$ (25). Then for every $t \in [t_1, t_2]$ there is an entry time $\theta \in [0, t_1]$ with $\tau(\theta) = t$ (the paper's $\theta = \tau_1^{-1}(t)$) such that
--
--   1. the volume is the inflow since $\theta$ (26):
--   $$\tau(t) = t + \alpha \int_{\theta}^{t} u(s)\,ds + \beta ;$$
--   2. $\tau$ has, relative to $[t_1, t_2]$, the derivative (28)
--   $$\tau'(t) = \alpha u(t) + \frac{1}{1 + \alpha u(\theta)} > \alpha u(t) .$$
--
--   Moreover $\tau$ is strictly increasing on $[t_1, t_2]$.
--
--   This is the second interval of the proof of Theorem 1, and the template of the induction step.
--
--   **Formalization Note** The paper treats the restriction $\tau_2$ of $\tau$ to $[t_1,t_2]$ as a separate function; here $\tau$ is one global function, so the junction identity (27), $\tau_2(t_1) = \tau_1(t_1)$, is automatic. Derivatives are taken within the closed interval $[t_1, t_2]$, since $\tau$ need not be differentiable at the junctions.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), pp. 185–186, proof of Theorem 1, (25)–(28)

import Mathlib
import Definitions.Def_FrieszDUE_FIFO_Setting

namespace FrieszDUE.FIFO

theorem second_interval_28 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u : ℝ → ℝ)
    (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (hu_cont : ContinuousOn u (Set.Ici 0))
    (τ : ℝ → ℝ) (hτ : IsLinearExitTime α β u τ) :
    tSeq τ 2 = τ (tSeq τ 1) ∧
      (∀ t ∈ Set.Icc (tSeq τ 1) (tSeq τ 2), ∃ θ ∈ Set.Icc 0 (tSeq τ 1), τ θ = t ∧
        τ t = t + α * (∫ s in θ..t, u s) + β ∧
        HasDerivWithinAt τ (α * u t + 1 / (1 + α * u θ)) (Set.Icc (tSeq τ 1) (tSeq τ 2)) t ∧
        α * u t < α * u t + 1 / (1 + α * u θ)) ∧
      StrictMonoOn τ (Set.Icc (tSeq τ 1) (tSeq τ 2)) := by sorry

end FrieszDUE.FIFO
