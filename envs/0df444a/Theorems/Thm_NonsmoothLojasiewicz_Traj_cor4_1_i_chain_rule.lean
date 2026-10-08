-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_cor4_1_i_chain_rule
-- name    : NonsmoothLojasiewicz.Traj.cor4_1_i_chain_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:37:11.047616+00:00
-- url     : https://prove2.me/theorems/a03d300e-4c45-489b-a167-4b625066e8ea
-- title:
--   Corollary 4.1(i) — chain rule $\frac{d}{dt}(f\circ x)(t)=\langle\dot x(t),x^*\rangle$ along trajectories
-- statement:
--   Assume the standing hypotheses of Section 4:
--
--   1. $(\mathcal H1)$ $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is either lower semicontinuous and convex, or lower-$C^2$ with $\operatorname{dom} f=\mathbb R^n$;
--   2. $(\mathcal H2)$ $f$ is somewhere finite and bounded from below.
--
--   Let $x:[0,T)\to\mathbb R^n$ be a trajectory of the subgradient system $\dot x(t)+\partial f(x(t))\ni 0$. Then for almost every $t\in(0,T)$, $x$ is differentiable at $t$, $f\circ x$ is differentiable at $t$, and
--   $$\frac{d}{dt}(f\circ x)(t)=\langle\dot x(t),x^*\rangle\qquad\text{for all }x^*\in\partial f(x(t)).$$
--
--   In particular, for almost every $t$ the map $x^*\mapsto\langle\dot x(t),x^*\rangle$ is constant on $\partial f(x(t))$ (Corollary 4.1(ii)). This chain rule is what makes $f$ a Lyapunov function of the system.
--
--   **Formalization Note** $\partial f(x(t))\neq\emptyset$ along a trajectory, so $f(x(t))$ is finite on $[0,T)$ and $f\circ x$ is the real-valued function $t\mapsto f(x(t))$. Convexity is the convexity of the epigraph (published `MoreauProx.Characterization.EConvex`); "bounded from below" is $f\ge m$ for a real $m$, which also excludes the value $-\infty$. $\dot x(t)$ is Lean's `deriv x t`, and the statement asserts that $x$ really has this derivative at $t$.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1218, Corollary 4.1(i) (standing assumptions (H1)–(H2), p. 1217)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NonsmoothLojasiewicz.Traj

open NonconvexSplitting.Shared

/-- Corollary 4.1(i) (p. 1218): under (𝓗1)–(𝓗2), for a trajectory `x` of (𝒢) on `[0, T)`, for
almost every `t ∈ (0, T)` the curve is differentiable at `t` and
`d/dt (f ∘ x)(t) = ⟨ẋ(t), x*⟩` for every `x* ∈ ∂f(x(t))`. -/
theorem cor4_1_i_chain_rule {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsTrajectory f x T) :
    ∀ᵐ t : ℝ, 0 < t → ENNReal.ofReal t < T →
      HasDerivAt x (deriv x t) t ∧
      ∀ v ∈ LimitingSubdiff f (x t),
        HasDerivAt (fun s => (f (x s)).toReal) ⟪deriv x t, v⟫_ℝ t := by sorry

end NonsmoothLojasiewicz.Traj
