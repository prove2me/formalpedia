-- Prove2me | Theorems.Thm_NonconvexSplitting_ADMMKL_semialgebraic_isKL
-- name    : NonconvexSplitting.ADMMKL.semialgebraic_isKL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T18:49:47.870597+00:00
-- url     : https://prove2.me/theorems/4ad9c807-e648-4372-8413-567747e9a6d2
-- title:
--   Proper closed semi-algebraic functions are KL functions
-- statement:
--   Let $f:\mathbb R^N\to(-\infty,+\infty]$ be proper, closed (lower semicontinuous) and semi-algebraic. Then $f$ is a KL function. Moreover, at every $\hat x\in\operatorname{dom}\partial f$ the KL property holds with the desingularizing function
--   $$
--   \varphi(s)=c\,s^{1-\theta}
--   $$
--   for some $\theta\in[0,1)$ and $c>0$: there are $\eta>0$ and a neighbourhood $V$ of $\hat x$ such that $\varphi'(f(x)-f(\hat x))\,\|v\|\ge1$ for all $x\in V$ with $f(\hat x)<f(x)<f(\hat x)+\eta$ and all $v\in\partial f(x)$.
--
--   This is the result the paper quotes from the literature (Attouch–Bolte–Redont–Soubeyran 2010, §4.3; Bolte–Daniilidis–Lewis 2007) to make Theorem 3 checkable; it is not proved in the paper.
--
--   **Formalization Note** KL function, limiting subdifferential and semi-algebraicity are as defined in this mission (the KL inequality ranges over all $v\in\partial f(x)$; $\eta$ is a positive real). $s^{1-\theta}$ is the real power `Real.rpow`.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 5, paragraph after Definition 1

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic
open NonconvexSplitting.Shared

open Filter Topology
open scoped InnerProductSpace

namespace NonconvexSplitting.ADMMKL

/-- Li–Pong (p. 5), quoting Attouch–Bolte–Redont–Soubeyran (2010, §4.3): a proper closed
semi-algebraic function `f : ℝᴺ → (-∞, +∞]` is a KL function; moreover at every point of
`dom ∂f` the KL property holds with `φ(s) = c s^{1-θ}` for some `θ ∈ [0, 1)` and `c > 0`. -/
theorem semialgebraic_isKL {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → EReal)
    (hprop : IsProperFn f) (hlsc : LowerSemicontinuous f) (hsa : IsSemialgebraicFn f) :
    IsKLFunction f ∧
      ∀ xhat, (LimitingSubdiff f xhat).Nonempty →
        ∃ c : ℝ, 0 < c ∧ ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ η : ℝ, 0 < η ∧ ∃ V ∈ 𝓝 xhat,
          KLIneq f xhat η V (fun s => c * s ^ (1 - θ)) := by sorry

end NonconvexSplitting.ADMMKL
