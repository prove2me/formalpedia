-- Prove2me | Theorems.Thm_NesterovODE_Restart_theorem_10
-- name    : NesterovODE.Restart.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:41:28.567312+00:00
-- url     : https://prove2.me/theorems/25b99a64-25ad-4eb6-88e2-962b783e3004
-- title:
--   Theorem 10, p. 22 — for f ∈ S_µ,L the speed restarted ODE satisfies f(Xˢʳ(t)) − f⋆ ≤ (c₁L‖x₀ − x⋆‖²/2) e^{−c₂t√L}
-- statement:
--   There exist positive constants $c_1$ and $c_2$, depending only on the condition number $L/\mu$, with the following property. Let $0<\mu\le L$, let $f\in\mathcal S_{\mu,L}$ on $\mathbb R^n$ with minimizer $x^\star$ and $f^\star=f(x^\star)$, let $x_0\in\mathbb R^n$, and let $X^{\mathrm{sr}}$ be the speed restarted trajectory from $x_0$, the solution of (29). Then for every $t\ge0$,
--
--   $$f(X^{\mathrm{sr}}(t))-f^\star\le\frac{c_1L\|x_0-x^\star\|^2}2\,e^{-c_2t\sqrt L}.$$
--
--   Resetting the friction of the Nesterov ODE whenever the speed stops increasing yields linear convergence for strongly convex objectives without knowledge of $\mu$, in contrast with the polynomial rates of the unrestarted ODE.
--
--   **Formalization Note** $c_1$ and $c_2$ are functions of the condition number, $c_i=c_i(L/\mu)$, chosen before the dimension, $f$, $\mu$, $L$, $x_0$ and the trajectory; this is "only depend on the condition number $L/\mu$". The statement covers every curve satisfying the speed-restart predicate of the Setting definition; in particular it covers $x_0=x^\star$, where the trajectory stays at $x^\star$. The predicate does not assume that the restart times tend to infinity: that is a consequence of Lemma 25.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 22, Theorem 10 (proof pp. 24–25)

import Mathlib
import Definitions.Def_NesterovODE_Restart_Setting

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Theorem 10 (p. 22): there are positive constants `c₁, c₂` depending only on the condition
number `L/μ` (functions of `L/μ`, chosen before the dimension, `f`, `μ`, `L`, `x₀`) such that
every speed restarted trajectory satisfies
`f(Xˢʳ(t)) − f⋆ ≤ (c₁L‖x₀ − x⋆‖²/2) e^{−c₂ t √L}` for all `t ≥ 0`. -/
theorem theorem_10 :
    ∃ c₁ c₂ : ℝ → ℝ, (∀ κ : ℝ, 0 < c₁ κ ∧ 0 < c₂ κ) ∧
      ∀ (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal),
        0 < μ → μ ≤ L → NesterovODE.StrongCvx.InSMuL μ L f →
        ∀ (x₀ xstar : NesterovODE.WellPosed.E n), (∀ y, f xstar ≤ f y) →
        ∀ Xsr : ℝ → NesterovODE.WellPosed.E n, IsSpeedRestarted f x₀ Xsr →
        ∀ t : ℝ, 0 ≤ t →
          f (Xsr t) - f xstar ≤
            c₁ (L / μ) * L * ‖x₀ - xstar‖ ^ 2 / 2 *
              Real.exp (-(c₂ (L / μ)) * t * Real.sqrt L) := by sorry

end NesterovODE.Restart
