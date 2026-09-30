-- Prove2me | Theorems.Thm_GoldenRatioVI_Explicit_prox_inequality
-- name    : GoldenRatioVI.Explicit.prox_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:29:03.220369+00:00
-- url     : https://prove2.me/theorems/540fb57e-4a2b-451a-8b91-7ae03163b025
-- title:
--   Eq. (4) — prox-inequality characterising $\bar x = \mathrm{prox}_g(w)$
-- statement:
--   Let $\mathcal E$ be a finite-dimensional real inner product space and let $g:\mathcal E\to(-\infty,+\infty]$ be proper, convex and lower semicontinuous. For $w,\bar x\in\mathcal E$,
--   $$\bar x = \operatorname{prox}_g(w) \iff \langle \bar x - w, x-\bar x\rangle \ge g(\bar x) - g(x)\quad \forall x\in\mathcal E. \tag{4}$$
--
--   This characteristic property of the proximal operator is used in every convergence proof of the paper; applied to $\lambda_k g$ it yields the inequalities (19)–(20) behind the energy estimate (27).
--
--   **Formalization Note** The right-hand side is written without extended-real subtraction as $g(\bar x)\le\langle\bar x-w,x-\bar x\rangle+g(x)$; it forces $\bar x\in\operatorname{dom} g$ (take $x\in\operatorname{dom} g$), as the left-hand side does.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 3, Eq. (4)

import Mathlib
import Definitions.Def_GoldenRatioVI_Explicit_viProblem
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace GoldenRatioVI.Explicit

/-- Eq. (4) of Malitsky (p. 3), the prox-inequality: for a proper convex lsc
`g : E → (−∞, +∞]`, `xbar = prox_g(w)` iff `⟨xbar − w, x − xbar⟩ ≥ g(xbar) − g(x)` for all `x`,
written without `EReal` subtraction as `g(xbar) ≤ ⟨xbar − w, x − xbar⟩ + g(x)`. -/
theorem prox_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (hg : IsProperConvexLSC g) (w xbar : E) :
    GoldenRatioVI.Shared.IsProxPoint g w xbar ↔
      ∀ x : E, g xbar ≤ ((inner ℝ (xbar - w) (x - xbar) : ℝ) : EReal) + g x := by sorry

end GoldenRatioVI.Explicit
