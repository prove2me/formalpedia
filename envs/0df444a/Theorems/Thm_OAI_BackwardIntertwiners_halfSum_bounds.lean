-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_halfSum_bounds
-- name    : OAI.BackwardIntertwiners.halfSum_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:29:23.14077+00:00
-- url     : https://prove2.me/theorems/af6e7b1f-fcfb-4c78-94f1-8142e60fc9f0
-- title:
--   Quadratic two-sided bounds for exponent sums with 2-adic residue corrections
-- statement:
--   Let $t:\mathbb{N}\to\mathbb{N}$ satisfy $t(m)<2^m$ for every $m\in\mathbb{N}$. For $k\ge1$ let $\kappa(k)=\lfloor\log_8 k\rfloor+1$, so that $\kappa(k)=q+1$ exactly when $8^q\le k<8^{q+1}$. Define the residue correction $\rho_t:\mathbb{N}\to\mathbb{R}$, the exponents $e_t:\mathbb{N}\to\mathbb{R}$ and their partial sums $S_t:\mathbb{N}\to\mathbb{R}$ by
--   $$\rho_t(0)=0,\qquad \rho_t(k)=100\bigl(2^{\kappa(k)}-2+t(\kappa(k))\bigr)\ (k\ge1),\qquad e_t(k)=10(k+1)+\rho_t(k),\qquad S_t(n)=\sum_{k=0}^{n-1}e_t(k).$$
--
--   **Theorem.** For every $n\in\mathbb{N}$,
--   $$5n(n+1)\;\le\;S_t(n)\;\le\;5n(n+1)+400\,n\sqrt{n}.$$
--
--   The correction $\rho_t$ is constant on each block $8^q\le k<8^{q+1}$ and stores the number $t(q+1)$ there; in the construction, $t(m)$ is either the residue of a 2-adic integer modulo $2^m$ or the complementary number $2^m-1$ minus that residue, so the exponent sums encode the 2-adic digits. The theorem says that this encoding perturbs the quadratic main term $5n(n+1)=\sum_{k<n}10(k+1)$ only by $O(n^{3/2})$; consequently $S_t(n)/n^2\to5$, which is the exact quadratic rate of the explicit weights $e^{-S_t(n)}$.
--
--   **Formalization Note** In Lean, $\kappa$ is `weightBlock k = Nat.log 8 k + 1`, $2^{\kappa(k)}$ is `residueScale k`, and $\rho_t$, $e_t$, $S_t$ are `residueCorrection t`, `halfExponent t`, `halfSum t`; the hypothesis is `ResidueBounds t`, i.e. `∀ m, t m < 2 ^ m`. The square root is `Real.sqrt` of the real cast of $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ExplicitWeights.lean#L115-L132

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.halfSum_bounds {t : ℕ → ℕ} (ht : ResidueBounds t) (n : ℕ) :
    5*(n:ℝ)*((n:ℝ)+1) ≤ halfSum t n ∧
    halfSum t n ≤ 5*(n:ℝ)*((n:ℝ)+1) + 400*(n:ℝ)*Real.sqrt n := by sorry
