-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Traj_ineq20_lojasiewicz_dom_subdiff
-- name    : NonsmoothLojasiewicz.Traj.ineq20_lojasiewicz_dom_subdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:08.089272+00:00
-- url     : https://prove2.me/theorems/6f1b622d-1467-4f27-93d4-40286a24022b
-- title:
--   Inequality (20) — the Łojasiewicz inequality around every point of $\operatorname{dom}\partial f$ under (H1)–(H3)
-- statement:
--   Assume $(\mathcal H1)$–$(\mathcal H3)$:
--
--   1. $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is either lower semicontinuous and convex, or lower-$C^2$ with $\operatorname{dom} f=\mathbb R^n$;
--   2. $f$ is somewhere finite and bounded from below;
--   3. $f$ is subanalytic.
--
--   Let $a\in\mathbb R^n$ with $\partial f(a)\neq\emptyset$. Then there exist $c>0$, $\theta\in[0,1)$ and $\varepsilon>0$ such that
--   $$|f(x)-f(a)|^{\theta}\le c\,m_f(x)\qquad\text{for all }x\in B(a,\varepsilon),$$
--   where $B(a,\varepsilon)$ is the open ball and $m_f$ the nonsmooth slope.
--
--   In the paper this is obtained from the main results of Section 3 when $a$ is critical and from Remarks 3.2 and 3.7 otherwise; it is the only place where subanalyticity enters the analysis of trajectories.
--
--   **Formalization Note** In the proof of Theorem 4.5 the function has been normalized so that $f(a)=0$ and (20) reads $|f(x)|^\theta\le c\,m_f(x)$; the statement here is the same inequality for the original $f$. "$\le c\,m_f(x)$" is written as "$\le c\|v\|$ for every $v\in\partial f(x)$", which is equivalent (and vacuous where $\partial f(x)=\emptyset$, where $m_f(x)=+\infty$). Where $\partial f(x)\neq\emptyset$, $f(x)$ is finite and its real value is used.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1220, proof of Theorem 4.5, inequality (20) (standing assumptions (H1)–(H3), pp. 1217, 1219)

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

/-- Inequality (20) (p. 1220): under (𝓗1)–(𝓗3), the Łojasiewicz inequality holds around every point
`a ∈ dom ∂f`: there are `c > 0`, `θ ∈ [0, 1)` and `ε > 0` with
`|f(x) - f(a)|^θ ≤ c m_f(x)` for all `x ∈ B(a, ε)` (written for every `x* ∈ ∂f(x)`). -/
theorem ineq20_lojasiewicz_dom_subdiff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (hH3 : IsSubanalyticFn f)
    (a : EuclideanSpace ℝ (Fin n)) (ha : (LimitingSubdiff f a).Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ Metric.ball a ε, ∀ v ∈ LimitingSubdiff f y,
        |(f y).toReal - (f a).toReal| ^ θ ≤ c * ‖v‖ := by sorry

end NonsmoothLojasiewicz.Traj
