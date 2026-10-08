-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_tail_length_bound
-- name    : NonsmoothLojasiewicz.Traj.tail_length_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:37:56.474575+00:00
-- url     : https://prove2.me/theorems/c52f306a-c1fe-436c-90af-d9f02195e0f3
-- title:
--   Section 4, the tail-length bound before (27): $\int_t^\infty\|\dot x\|\le \frac{c}{1-\theta}(f(x(t))-f(a))^{1-\theta}$
-- statement:
--   Assume $(\mathcal H1)$–$(\mathcal H3)$ ($f$ lower semicontinuous convex or lower-$C^2$ with full domain; somewhere finite and bounded below; subanalytic). Let $x$ be a maximal trajectory of $\dot x(t)+\partial f(x(t))\ni0$ that converges to a point $a$ as $t\to+\infty$, and let $c>0$, $\theta\in[0,1)$, $\varepsilon>0$ be constants for which inequality (20) holds around $a$:
--   $$|f(y)-f(a)|^\theta\le c\,m_f(y)\qquad\text{for all }y\in B(a,\varepsilon).$$
--   Then there is $t_0\ge0$ such that for every $t\ge t_0$
--   $$\int_t^{+\infty}\|\dot x(s)\|\,ds\ \le\ \frac{c}{1-\theta}\,\big(f(x(t))-f(a)\big)^{1-\theta}.$$
--
--   The tail length of the trajectory is thus controlled by the gap in function value; this is the bridge from the Łojasiewicz inequality to the convergence rates of Theorem 4.7.
--
--   **Formalization Note** The paper has normalized $f(a)=0$, so its display reads $\frac{c}{1-\theta}f(x(t_0))^{1-\theta}$; the statement is the same for the original $f$. Along the trajectory $f(x(t))$ decreases to $f(a)$, so the base $f(x(t))-f(a)$ is nonnegative. The integral is the lower Lebesgue integral of $\|\dot x\|$ (Lean's `deriv`) in $[0,+\infty]$, compared with the real right-hand side cast to $[0,+\infty]$. (20) is written for every subgradient $v\in\partial f(y)$.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1221, Section 4, the inequality displayed before (27) and the sentence after it (with (20), p. 1220)

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

/-- Section 4, the inequality displayed before (27) (p. 1221): under (𝓗1)–(𝓗3), let `x` be a
maximal trajectory of (𝒢) converging to `a`, and let `c > 0`, `θ ∈ [0, 1)`, `ε > 0` be
constants for which (20) holds around `a`. Then there is `t₀ ≥ 0` such that for every `t ≥ t₀`,
`∫ₜ^∞ ‖ẋ(s)‖ ds ≤ c/(1-θ) · (f(x(t)) - f(a))^{1-θ}`. -/
theorem tail_length_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (hH3 : IsSubanalyticFn f)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsMaximalTrajectory f x T)
    (a : EuclideanSpace ℝ (Fin n)) (hxa : Tendsto x atTop (𝓝 a))
    (c θ ε : ℝ) (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (h20 : ∀ y ∈ Metric.ball a ε, ∀ v ∈ LimitingSubdiff f y,
      |(f y).toReal - (f a).toReal| ^ θ ≤ c * ‖v‖) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      ∫⁻ s in Set.Ioi t, ‖deriv x s‖ₑ ≤
        ENNReal.ofReal (c / (1 - θ) * ((f (x t)).toReal - (f a).toReal) ^ (1 - θ)) := by sorry

end NonsmoothLojasiewicz.Traj
