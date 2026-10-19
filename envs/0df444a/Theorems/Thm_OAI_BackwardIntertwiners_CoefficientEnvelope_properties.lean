-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_CoefficientEnvelope_properties
-- name    : OAI.BackwardIntertwiners.CoefficientEnvelope.properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:19:44.195466+00:00
-- url     : https://prove2.me/theorems/a65302e8-4919-43a4-aa04-9780117919be
-- title:
--   Basic properties of the convex envelope of a coefficient sequence
-- statement:
--   A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its increments $F(n+1)-F(n)$ form a nondecreasing sequence, equivalently if its second differences $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ are all $\ge0$. For a sequence $d:\mathbb{N}\to\mathbb{C}$, let $I_d=\{n\ge1:d_n\neq0\}$ and define the *coefficient envelope* $\Phi_d:\mathbb{N}\to\mathbb{R}$ as the discrete convex envelope of $n\mapsto-\log|d_n|$ on $I_d$:
--   $$\Phi_d(n)=\sup\Bigl\{F(n)\ :\ F(0)=0,\ F\text{ discretely convex},\ F(k)\le-\log|d_k|\ \text{for every }k\ge1\text{ with }d_k\neq0\Bigr\}.$$
--
--   Let $d:\mathbb{N}\to\mathbb{C}$ have nonzero terms beyond every index (for every $n$ there is $k>n$ with $d_k\neq0$), and let $G:\mathbb{N}\to\mathbb{R}$ be discretely convex with $G(0)=0$ and $|d_n|\le e^{-G(n)}$ for all $n\in\mathbb{N}$. Then:
--   1. $\Phi_d(0)=0$;
--   2. $\Phi_d$ is discretely convex;
--   3. $G(n)\le\Phi_d(n)$ for all $n$;
--   4. $|d_n|\le e^{-\Phi_d(n)}$ for all $n$;
--   5. for every $n$, if $\Phi_d(n+2)-2\Phi_d(n+1)+\Phi_d(n)>0$, then $|d_{n+1}|=e^{-\Phi_d(n+1)}$.
--
--   Thus $\Phi_d$ is a normalized convex profile that still controls the coefficients, improves on any given convex profile $G$, and is attained at each of its strict corners. In the project, given profiles in envelope bounds are replaced by coefficient envelopes so that the contact conditions required by the correlation obstruction hold.
--
--   **Formalization Note** $I_d$ is `coefficientObstacle d` and $\Phi_d$ is `coefficientEnvelope d`, the `convexEnvelope` of $n\mapsto-\log\|d_n\|$ on $I_d$. Lean's convention $\log0=0$ is irrelevant, because the obstacle is only imposed at indices where $d_n\neq0$; the index $0$ is excluded from $I_d$. The envelope is defined with `sSup`, and under the hypotheses its defining sets are nonempty and bounded above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean#L38-L64

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
variable {d : ℕ → ℂ} {G : ℕ → ℝ}
variable (hu : ∀ n : ℕ, ∃ k, n < k ∧ d k ≠ 0)
variable (hG : DiscreteConvex G) (hG0 : G 0 = 0)
variable (hb : ∀ n, ‖d n‖ ≤ Real.exp (-G n))

include hu hG hG0 hb in
theorem OAI.BackwardIntertwiners.CoefficientEnvelope.properties :
    coefficientEnvelope d 0 = 0 ∧ DiscreteConvex (coefficientEnvelope d) ∧
    (∀ n, G n ≤ coefficientEnvelope d n) ∧
    (∀ n, ‖d n‖ ≤ Real.exp (-coefficientEnvelope d n)) ∧
    (∀ n, 0 < coefficientEnvelope d (n+2) - 2*coefficientEnvelope d (n+1) +
      coefficientEnvelope d n → ‖d (n+1)‖ = Real.exp (-coefficientEnvelope d (n+1))) := by sorry
