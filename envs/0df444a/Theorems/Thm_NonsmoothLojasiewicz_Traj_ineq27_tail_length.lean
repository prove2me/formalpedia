-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_ineq27_tail_length
-- name    : NonsmoothLojasiewicz.Traj.ineq27_tail_length
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:08.142065+00:00
-- url     : https://prove2.me/theorems/b6bc9c54-0524-4745-9ffb-924967a880d5
-- title:
--   Inequality (27) — $\int_t^\infty\|\dot x\|\le\frac{k}{1-\theta}\|\dot x(t)\|^{(1-\theta)/\theta}$ with $k=c^{1/\theta}$
-- statement:
--   Assume $(\mathcal H1)$–$(\mathcal H3)$ ($f$ lower semicontinuous convex or lower-$C^2$ with full domain; somewhere finite and bounded below; subanalytic). Let $x$ be a maximal trajectory of $\dot x(t)+\partial f(x(t))\ni0$ converging to $a$, and let $c>0$, $\theta\in(0,1)$, $\varepsilon>0$ be constants for which (20) holds around $a$:
--   $$|f(y)-f(a)|^\theta\le c\,m_f(y)\qquad\text{for all }y\in B(a,\varepsilon).$$
--   Put $k=c^{1/\theta}$. Then there is $t_0\ge0$ such that for almost every $t\ge t_0$
--   $$\int_t^{+\infty}\|\dot x(s)\|\,ds\ \le\ \frac{k}{1-\theta}\,\|\dot x(t)\|^{\frac{1-\theta}{\theta}} .$$
--
--   Read as a differential inequality for the tail length $\sigma(t)=\int_t^{+\infty}\|\dot x(s)\|\,ds$, this is the inequality from which the rates of Theorem 4.7 are integrated.
--
--   **Formalization Note** The paper writes "for all $t\ge t_0$"; $\dot x(t)$ exists only for almost every $t$, and at a time where $x$ is not differentiable Lean's `deriv` is $0$, which would assert a zero tail, so the statement is for almost every $t\ge t_0$. The constant $k=c^{1/\theta}$ is the printed one. The integral is a lower Lebesgue integral in $[0,+\infty]$.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1221, Section 4, inequality (27) (with (20), p. 1220)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory
import Definitions.Def_NonsmoothLojasiewicz_Traj_Subanalytic

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NonsmoothLojasiewicz.Traj

open NonconvexSplitting.Shared

/-- Inequality (27) (p. 1221): in the setting of the tail-length bound, with `θ ∈ (0, 1)` and
`k = c^{1/θ}`, there is `t₀ ≥ 0` such that for almost every `t ≥ t₀`,
`∫ₜ^∞ ‖ẋ(s)‖ ds ≤ k/(1-θ) · ‖ẋ(t)‖^{(1-θ)/θ}`. -/
theorem ineq27_tail_length {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (hH3 : IsSubanalyticFn f)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsMaximalTrajectory f x T)
    (a : EuclideanSpace ℝ (Fin n)) (hxa : Tendsto x atTop (𝓝 a))
    (c θ ε : ℝ) (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (h20 : ∀ y ∈ Metric.ball a ε, ∀ v ∈ LimitingSubdiff f y,
      |(f y).toReal - (f a).toReal| ^ θ ≤ c * ‖v‖) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ᵐ t : ℝ, t₀ ≤ t →
      ∫⁻ s in Set.Ioi t, ‖deriv x s‖ₑ ≤
        ENNReal.ofReal (c ^ (1 / θ) / (1 - θ) * ‖deriv x t‖ ^ ((1 - θ) / θ)) := by sorry

end NonsmoothLojasiewicz.Traj
