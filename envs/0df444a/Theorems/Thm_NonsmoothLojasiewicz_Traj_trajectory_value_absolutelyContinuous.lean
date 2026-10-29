-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_trajectory_value_absolutelyContinuous
-- name    : NonsmoothLojasiewicz.Traj.trajectory_value_absolutelyContinuous
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-29T00:26:32.2764+00:00
-- url     : https://prove2.me/theorems/db92d491-0d6a-4235-b6d2-562adfad056c
-- title:
--   The value $f\circ x$ along a trajectory of $\dot x+\partial f(x)\ni 0$ is absolutely continuous
-- statement:
--   Assume $(\mathcal H1)$–$(\mathcal H2)$: $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is either lower semicontinuous and convex, or lower-$C^2$ with $\operatorname{dom} f=\mathbb R^n$; and $f$ is somewhere finite and bounded from below. Let $x:[0,T)\to\mathbb R^n$ be a trajectory of the subgradient system $(\mathcal G)$, i.e. $x$ is absolutely continuous, $\dot x(t)+\partial f(x(t))\ni 0$ for almost every $t\in(0,T)$, and $\partial f(x(t))\neq\emptyset$ for every $t\in[0,T)$. Then the function
--
--   $$h:=f\circ x$$
--
--   is absolutely continuous on every compact interval $[0,b]\subset[0,T)$.
--
--   Role: this is the Lyapunov-function regularity that, together with the chain rule of Corollary 4.1(i), gives $f(x(s))-f(x(t))=\int_s^t\|\dot x\|^2$ along a trajectory; Theorem 4.5 needs it to integrate the Łojasiewicz differential inequality for $(f\circ x)^{1-\theta}$.
--
--   **Formalization Note**: $f(x(t))$ is finite for $t\in[0,T)$ because $\partial f(x(t))\neq\emptyset$ forces $f(x(t))<+\infty$ and $f$ is bounded below, so `toReal` is faithful on $[0,b]$. The page states the property for the trajectory issued from $x_0$; trajectories with a given initial point are unique under $(\mathcal H1)$–$(\mathcal H2)$ (same paragraph), so it holds for every trajectory.
-- source:
--   J. Bolte, A. Daniilidis, A. Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, https://people.orie.cornell.edu/aslewis/publications/07-lojasiewicz.pdf, Section 4, p. 1217, paragraph 'Existence of trajectories' (last sentence: 'In addition, the function h := f ∘ x is absolutely continuous'), citing Brézis, Opérateurs maximaux monotones (1973), Thm 3.2 p. 57 and Prop. 3.12 p. 106

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NonsmoothLojasiewicz.Traj

theorem trajectory_value_absolutelyContinuous {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsTrajectory f x T)
    (b : ℝ) (hb0 : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    AbsolutelyContinuousOnInterval (fun t => (f (x t)).toReal) 0 b := by sorry

end NonsmoothLojasiewicz.Traj
