-- Prove2me | Theorems.Thm_FrieszDUE_FIFO_induction_step_34
-- name    : FrieszDUE.FIFO.induction_step_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:21:35.578828+00:00
-- url     : https://prove2.me/theorems/9f4e6f3f-407c-43b4-bff6-8bc64c83377f
-- title:
--   (29)–(37), p. 186 — on every [t_{n+1}, t_{n+2}]: τ(t) = t + α∫_{τ⁻¹(t)}ᵗ u + β, τ′ > αu(t), τ strictly increasing
-- statement:
--   Let $\alpha, \beta > 0$, let the entry rate $u$ be nonnegative and continuous on $[0, \infty)$, and let $\tau$ satisfy the exit-time equation $\tau(t) = t + \alpha x(t) + \beta$ for $t \ge 0$, with $x(t)$ the mass of the vehicles on the arc at time $t$. Let $t_0 = 0$ and $t_{k+1} = \tau(t_k)$. Then for every $n \ge 0$:
--
--   1. for every $t \in [t_{n+1}, t_{n+2}]$ there is $\theta \in [t_n, t_{n+1}]$ with $\tau(\theta) = t$ and
--   $$\tau(t) = t + \alpha \int_{\theta}^{t} u(s)\,ds + \beta \qquad (29), (32);$$
--   2. at every $t \in [t_{n+1}, t_{n+2}]$, $\tau$ has a derivative relative to $[t_{n+1}, t_{n+2}]$ and
--   $$\tau'(t) > \alpha u(t) \qquad (31), (34);$$
--   3. $\tau$ is strictly increasing on $[t_{n+1}, t_{n+2}]$.
--
--   This is the outcome of the induction in the proof of Theorem 1; the case $n = 0$ is the second interval (28).
--
--   **Formalization Note** The paper's induction runs over separate pieces $\tau_k : [t_{k-1}, t_k] \to \mathbb R$ with the junction conditions (30), (33). Here $\tau$ is one global function, so the junction conditions are automatic and the statement is the conclusion of the induction for every interval, rather than the step "(29)–(31) for $k \le n$ imply (33)–(34)". Derivatives are one-sided at the endpoints of each interval.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 186, proof of Theorem 1, (29)–(37)

import Mathlib
import Definitions.Def_FrieszDUE_FIFO_Setting

namespace FrieszDUE.FIFO

theorem induction_step_34 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u : ℝ → ℝ)
    (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (hu_cont : ContinuousOn u (Set.Ici 0))
    (τ : ℝ → ℝ) (hτ : IsLinearExitTime α β u τ) (n : ℕ) :
    (∀ t ∈ Set.Icc (tSeq τ (n + 1)) (tSeq τ (n + 2)),
      ∃ θ ∈ Set.Icc (tSeq τ n) (tSeq τ (n + 1)), τ θ = t ∧
        τ t = t + α * (∫ s in θ..t, u s) + β ∧
        ∃ d : ℝ, HasDerivWithinAt τ d (Set.Icc (tSeq τ (n + 1)) (tSeq τ (n + 2))) t ∧
          α * u t < d) ∧
      StrictMonoOn τ (Set.Icc (tSeq τ (n + 1)) (tSeq τ (n + 2))) := by sorry

end FrieszDUE.FIFO
