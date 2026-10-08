-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_thm4_7_convergence_rates
-- name    : NonsmoothLojasiewicz.Traj.thm4_7_convergence_rates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:11.115912+00:00
-- url     : https://prove2.me/theorems/5e6f0069-fc7a-4b78-992c-7ae1157da667
-- title:
--   Theorem 4.7 — bounded subgradient trajectories converge with Łojasiewicz rates
-- statement:
--   Assume $(\mathcal H1)$–$(\mathcal H3)$:
--
--   1. $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is either lower semicontinuous and convex, or lower-$C^2$ with $\operatorname{dom} f=\mathbb R^n$;
--   2. $f$ is somewhere finite and bounded from below;
--   3. $f$ is subanalytic.
--
--   Let $x:[0,T)\to\mathbb R^n$ be a bounded maximal trajectory of the subgradient system $\dot x(t)+\partial f(x(t))\ni0$. Then $T=+\infty$ and $x(t)$ converges to some critical point $a$ of $f$. Moreover, let $\theta\in[0,1)$ be any Łojasiewicz exponent of $f$ at $a$, i.e. $|f(y)-f(a)|^\theta/m_f(y)$ is bounded near $a$. Then there exist $k>0$, $k'>0$ and $t_0\ge0$ such that for all $t\ge t_0$:
--
--   1. if $\theta\in(\tfrac12,1)$, then $$\|x(t)-a\|\le k\,(t+1)^{-\frac{1-\theta}{2\theta-1}};$$
--   2. if $\theta=\tfrac12$, then $$\|x(t)-a\|\le k\,e^{-k't};$$
--   3. if $\theta\in[0,\tfrac12)$, then $x(t)$ converges in finite time: $x(t)=a$ for all sufficiently large $t$.
--
--   This is the nonsmooth counterpart of the classical Łojasiewicz convergence-rate theorem for gradient flows of real-analytic functions, covering convex and lower-$C^2$ subanalytic objectives, possibly with value $+\infty$ in the convex case.
--
--   **Formalization Note** $T=+\infty$ (Corollary 4.1(iii)) is stated as part of the conclusion, since convergence and "for all $t\ge t_0$" refer to $t\to+\infty$; maximality, not $T=+\infty$, is the hypothesis. The rates hold for every Łojasiewicz exponent $\theta$ at the limit $a$, and $k,k',t_0$ may depend on $\theta$ and on the trajectory. A Łojasiewicz exponent is encoded as $\theta\in[0,1)$ with $|f(y)-f(a)|^\theta\le C\|v\|$ for all $y$ near $a$ and $v\in\partial f(y)$, with $0^0=1$; at a critical point this excludes $\theta=0$, so the third case concerns $\theta\in(0,\tfrac12)$ in practice, as in the paper's proof. Boundedness is of the image of $[0,T)$.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1221, Theorem 4.7 (standing assumptions (H1)–(H3), pp. 1217, 1219; Łojasiewicz exponent, p. 1221)

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

/-- Theorem 4.7 (p. 1221): under (𝓗1)–(𝓗3), let `x` be a bounded maximal trajectory of (𝒢).
Then `x` is defined on all of `ℝ₊` (Corollary 4.1(iii)) and converges to some critical point
`a` of `f`. For every Łojasiewicz exponent `θ ∈ [0, 1)` of `f` at `a` there are `k > 0`,
`k' > 0` and `t₀ ≥ 0` such that for all `t ≥ t₀`:
* if `θ ∈ (1/2, 1)`, then `‖x(t) - a‖ ≤ k (t + 1)^{-(1-θ)/(2θ-1)}`;
* if `θ = 1/2`, then `‖x(t) - a‖ ≤ k exp(-k' t)`;
* if `θ ∈ [0, 1/2)`, then `x` converges in finite time (is eventually equal to `a`). -/
theorem thm4_7_convergence_rates {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (hH3 : IsSubanalyticFn f)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsMaximalTrajectory f x T)
    (hbdd : Bornology.IsBounded (x '' timeDom T)) :
    T = ⊤ ∧ ∃ a ∈ NonsmoothLojasiewicz.Continuous.crit f, Tendsto x atTop (𝓝 a) ∧
      ∀ θ : ℝ, IsLojExponent f a θ →
        ∃ k : ℝ, 0 < k ∧ ∃ k' : ℝ, 0 < k' ∧ ∃ t₀ : ℝ, 0 ≤ t₀ ∧
          (1 / 2 < θ → ∀ t : ℝ, t₀ ≤ t →
            ‖x t - a‖ ≤ k * (t + 1) ^ (-((1 - θ) / (2 * θ - 1)))) ∧
          (θ = 1 / 2 → ∀ t : ℝ, t₀ ≤ t → ‖x t - a‖ ≤ k * Real.exp (-k' * t)) ∧
          (θ < 1 / 2 → ∃ t₁ : ℝ, ∀ t : ℝ, t₁ ≤ t → x t = a) := by sorry

end NonsmoothLojasiewicz.Traj
