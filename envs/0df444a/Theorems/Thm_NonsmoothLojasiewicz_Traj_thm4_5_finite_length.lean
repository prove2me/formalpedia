-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_thm4_5_finite_length
-- name    : NonsmoothLojasiewicz.Traj.thm4_5_finite_length
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:37:44.994141+00:00
-- url     : https://prove2.me/theorems/3ebf3a15-301b-4312-b793-e4b73e4e9210
-- title:
--   Theorem 4.5 — bounded maximal subgradient trajectories have finite length and converge to a critical point
-- statement:
--   Assume $(\mathcal H1)$–$(\mathcal H3)$:
--
--   1. $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is either lower semicontinuous and convex, or lower-$C^2$ with $\operatorname{dom} f=\mathbb R^n$;
--   2. $f$ is somewhere finite and bounded from below;
--   3. $f$ is subanalytic.
--
--   Let $x:[0,T)\to\mathbb R^n$ be a maximal trajectory of $\dot x(t)+\partial f(x(t))\ni0$ whose image $x([0,T))$ is bounded. Then $T=+\infty$, the trajectory has finite length,
--   $$\int_0^{+\infty}\|\dot x(t)\|\,dt<+\infty,$$
--   and $x(t)$ converges as $t\to+\infty$ to some critical point $a\in\operatorname{crit} f$, i.e. $0\in\partial f(a)$.
--
--   Without subanalyticity a bounded trajectory has cluster points but need not converge; the Łojasiewicz inequality rules this out.
--
--   **Formalization Note** The conclusion $T=+\infty$ is Corollary 4.1(iii) made explicit (the proof opens with "the trajectory is defined over all $\mathbb R_+$"); it is needed for "converges" and "length" to refer to $t\to+\infty$. Maximality is a hypothesis, $T=+\infty$ is not. The length is the lower Lebesgue integral of $\|\dot x\|$ in $[0,+\infty]$, so "finite length" is a genuine condition. Boundedness is of the image of $[0,T)$ only.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1219, Theorem 4.5 (standing assumptions (H1)–(H3), pp. 1217, 1219)

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

/-- Theorem 4.5 (p. 1219): under (𝓗1)–(𝓗3), any bounded maximal trajectory of (𝒢) is defined on
all of `ℝ₊` (Corollary 4.1(iii)), has finite length `∫₀^∞ ‖ẋ(t)‖ dt < +∞`, and converges to some
critical point of `f`. -/
theorem thm4_5_finite_length {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (hH3 : IsSubanalyticFn f)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsMaximalTrajectory f x T)
    (hbdd : Bornology.IsBounded (x '' timeDom T)) :
    T = ⊤ ∧ ∫⁻ t in Set.Ioi (0 : ℝ), ‖deriv x t‖ₑ < ⊤ ∧
      ∃ a ∈ NonsmoothLojasiewicz.Continuous.crit f, Tendsto x atTop (𝓝 a) := by sorry

end NonsmoothLojasiewicz.Traj
