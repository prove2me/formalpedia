-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_cor4_2_slow_solution
-- name    : NonsmoothLojasiewicz.Traj.cor4_2_slow_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:37:46.016302+00:00
-- url     : https://prove2.me/theorems/ba1a57c6-a2ed-4fea-963d-fa866485054f
-- title:
--   Corollary 4.2 — $\|\dot x(t)\|=m_f(x(t))$ and $\frac{d}{dt}(f\circ x)(t)=-m_f(x(t))^2$
-- statement:
--   Assume $(\mathcal H1)$–$(\mathcal H2)$: $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is either lower semicontinuous and convex, or lower-$C^2$ with $\operatorname{dom} f=\mathbb R^n$; and $f$ is somewhere finite and bounded from below. Let $m_f(y)=\inf\{\|y^*\|: y^*\in\partial f(y)\}$ be the nonsmooth slope.
--
--   Let $x$ be a maximal trajectory of $\dot x(t)+\partial f(x(t))\ni0$. Then for almost every time $t$ of its domain,
--   $$\|\dot x(t)\|=m_f(x(t))\qquad\text{and}\qquad \frac{d}{dt}(f\circ x)(t)=-\big[m_f(x(t))\big]^2 .$$
--
--   Thus trajectories are "slow solutions": the velocity is minus the least-norm subgradient, and $f$ decreases along trajectories at rate $m_f^2$.
--
--   **Formalization Note** The page says "for almost all $t\in\mathbb R_+$"; by Corollary 4.1(iii) the domain $[0,T)$ of a maximal trajectory is $\mathbb R_+$, and the statement is written for almost every $t\in(0,T)$ so that it does not presuppose that fact. $m_f(x(t))$ is finite because $\partial f(x(t))\neq\emptyset$, so its real value is used. $\dot x(t)$ is Lean's `deriv x t`, meaningful almost everywhere.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1218, Corollary 4.2 (standing assumptions (H1)–(H2), p. 1217)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NonsmoothLojasiewicz.Traj

/-- Corollary 4.2 (p. 1218): under (𝓗1)–(𝓗2), along a maximal trajectory `x` of (𝒢), for almost
every time `t` of its domain, `‖ẋ(t)‖ = m_f(x(t))` and `d/dt (f ∘ x)(t) = -[m_f(x(t))]²`.
(`m_f(x(t))` is finite since `∂f(x(t)) ≠ ∅`.) -/
theorem cor4_2_slow_solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsMaximalTrajectory f x T) :
    ∀ᵐ t : ℝ, 0 < t → ENNReal.ofReal t < T →
      ‖deriv x t‖ = (NonsmoothLojasiewicz.Continuous.slope f (x t)).toReal ∧
      HasDerivAt (fun s => (f (x s)).toReal) (-((NonsmoothLojasiewicz.Continuous.slope f (x t)).toReal ^ 2)) t := by sorry

end NonsmoothLojasiewicz.Traj
