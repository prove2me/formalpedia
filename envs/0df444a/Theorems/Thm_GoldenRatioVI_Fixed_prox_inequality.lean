-- Prove2me | Theorems.Thm_GoldenRatioVI_Fixed_prox_inequality
-- name    : GoldenRatioVI.Fixed.prox_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:56:18.157814+00:00
-- url     : https://prove2.me/theorems/b062dd78-9db2-49e0-9eca-16c94ecc3d4f
-- title:
--   Eq. (4) — prox-inequality characterising $\operatorname{prox}_g$
-- statement:
--   Let $\mathcal E$ be a finite-dimensional real inner product space and $g:\mathcal E\to(-\infty,+\infty]$ a proper convex lower semicontinuous function. For all $z,\bar x\in\mathcal E$,
--   $$\bar x = \operatorname{prox}_g z \quad\Longleftrightarrow\quad \langle \bar x - z, x - \bar x\rangle \ \ge\ g(\bar x) - g(x) \qquad \forall x\in\mathcal E.$$
--
--   This variational characterisation of the proximal point is the tool the convergence proof applies (to $\lambda g$) at every iteration of the algorithm.
--
--   **Formalization Note** "$\bar x = \operatorname{prox}_g z$" is the argmin predicate `IsProxPoint g z xbar`. The right side is evaluated in `EReal`: when $g(x)=+\infty$ and $g(\bar x)<+\infty$ the difference is $-\infty$ and the inequality holds; since $g$ is proper, the right side for all $x$ forces $g(\bar x)<+\infty$, so the value $\infty-\infty$ never decides the equivalence.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 3, Eq. (4)

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace GoldenRatioVI.Fixed

/-- Eq. (4), the prox-inequality: for a proper convex lsc `g : E → (-∞, +∞]`,
`x̄ = prox_g z ⇔ ⟪x̄ - z, x - x̄⟫ ≥ g(x̄) - g(x)` for all `x ∈ E`. -/
theorem prox_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (hg : IsProperConvexLSC g) (z xbar : E) :
    GoldenRatioVI.Shared.IsProxPoint g z xbar ↔
      ∀ x : E, ((inner ℝ (xbar - z) (x - xbar) : ℝ) : EReal) ≥ g xbar - g x := by sorry

end GoldenRatioVI.Fixed
