-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_cor4_1_iii_maximal_extension
-- name    : NonsmoothLojasiewicz.Traj.cor4_1_iii_maximal_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:37:20.318649+00:00
-- url     : https://prove2.me/theorems/0373f612-f223-44e4-81bc-e3454f8b508c
-- title:
--   Corollary 4.1(iii) — every trajectory extends to a maximal one on $\mathbb R_+$ with $\dot x\in L^2$
-- statement:
--   Assume $(\mathcal H1)$–$(\mathcal H2)$: $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is either lower semicontinuous and convex, or lower-$C^2$ with $\operatorname{dom} f=\mathbb R^n$; and $f$ is somewhere finite and bounded from below.
--
--   Let $x:[0,T)\to\mathbb R^n$ be a trajectory of $\dot x(t)+\partial f(x(t))\ni 0$. Then $x$ can be extended to a maximal trajectory $\hat x$ defined on all of $\mathbb R_+=[0,+\infty)$, with square-integrable velocity:
--   $$\hat x=x\ \text{on }[0,T),\qquad \int_0^{+\infty}\|\dot{\hat x}(t)\|^2\,dt<+\infty .$$
--
--   Consequently every maximal trajectory is defined on all of $\mathbb R_+$, which is what makes the asymptotic statements of Theorems 4.5 and 4.7 meaningful.
--
--   **Formalization Note** The paper writes $\hat x\in W^{1,2}(\mathbb R_+;\mathbb R^n)$. Read literally this would also require $\hat x\in L^2(\mathbb R_+)$, which fails for any trajectory converging to a nonzero point (e.g. $f=\tfrac12\|\cdot-a\|^2$, $a\neq0$); the proof establishes exactly that the maximal extension lives on $(0,+\infty)$ and that $\dot{\hat x}\in L^2$, which is what is stated. The integral is a lower Lebesgue integral of $\|\dot{\hat x}\|^2$ in $[0,+\infty]$ (Lean's `deriv`), so finiteness is a genuine condition.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1218, Corollary 4.1(iii) (standing assumptions (H1)–(H2), p. 1217)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NonsmoothLojasiewicz.Traj

/-- Corollary 4.1(iii) (p. 1218), read as: under (𝓗1)–(𝓗2), every trajectory `x` of (𝒢) on
`[0, T)` extends to a maximal trajectory `x̂` defined on all of `ℝ₊ = [0, +∞)` whose velocity
is square integrable on `(0, +∞)`. -/
theorem cor4_1_iii_maximal_extension {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsTrajectory f x T) :
    ∃ xhat : ℝ → EuclideanSpace ℝ (Fin n),
      (∀ t ∈ timeDom T, xhat t = x t) ∧
      IsMaximalTrajectory f xhat ⊤ ∧
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖deriv xhat t‖ₑ ^ 2 < ⊤ := by sorry

end NonsmoothLojasiewicz.Traj
