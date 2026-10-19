-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_quadratic_support_separation
-- name    : OAI.BackwardIntertwiners.quadratic_support_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:24:59.498567+00:00
-- url     : https://prove2.me/theorems/26adcb1d-6843-4071-9d78-743899d02487
-- title:
--   Support separation for weights with exact quadratic log-growth rate above $\log 3$
-- statement:
--   Let $w:\mathbb{Z}\to\mathbb{R}$. A function $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if $F(n+1)-F(n)$ is nondecreasing in $n$. Call $w$ a **quadratic weight** if
--
--   1. $w(j)>0$ for every $j\in\mathbb{Z}$;
--   2. $w$ is nonincreasing on $\mathbb{Z}$;
--   3. $n\mapsto\log w(-n)$ is discretely convex on $\mathbb{N}$;
--   4. $n\mapsto-\log w(n)$ is discretely convex on $\mathbb{N}$;
--   5. the family $\bigl(w(j)^{1/j}\bigr)_{j\in\mathbb{Z},\,j\neq0}$ is summable;
--   6. there is a real number $a>\log 3$ such that $\log w(n)/n^2\to-a$ and $\log w(-n)/n^2\to a$ as $n\to\infty$ through $\mathbb{N}$.
--
--   Say that $w$ has the **support separation property** if for all $b,c:\mathbb{Z}\to\mathbb{C}$, neither identically zero, with $|b_j|\le w(j)$ and $|c_j|\,w(j)\le1$ for all $j\in\mathbb{Z}$ and with $\sum_{j\in\mathbb{Z}}b_jc_{j-r}=0$ for every integer $r\ge1$, there exist integers $t,h$ such that $b_t\neq0$, $c_h\neq0$, $b_j=0$ for all $j>t$, $c_j=0$ for all $j<h$, and $t\le h$.
--
--   **Theorem.** Every quadratic weight $w$ has the support separation property. Explicitly, for all $b,c$ as in that definition,
--   $$\exists\, t,h\in\mathbb{Z}:\qquad b_t\neq0,\quad c_h\neq0,\quad b_j=0\ (j>t),\quad c_j=0\ (j<h),\quad t\le h .$$
--
--   Thus no normalization $w(0)=1$ and no explicit choice of constants is needed: an exact quadratic rate $a>\log 3$ for $\log w$ on both sides, together with the convexity conditions, suffices. This is the form of the support separation theorem that is applied, fiber by fiber, to the explicit weights of the weighted shifts in this construction, where it turns orthogonality relations into an ordering of supports.
--
--   **Formalization Note** Quadratic weights are the structure `QuadraticWeights w` with fields `positive`, `decreasing`, `convex_negative`, `concave_positive`, `root_sum` and `quadratic`; in `root_sum` the power $w(j)^{1/j}$ is `Real.rpow` with real exponent `1 / (j : ℝ)` and the $j=0$ term is replaced by $0$. The correlation sums are `tsum`s, equal to $0$ for non-summable families. The conclusion is `SupportSeparation w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/WeightSeparation.lean#L184-L257

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.quadratic_support_separation (w : ℤ → ℝ) (hw : QuadraticWeights w) :
    SupportSeparation w := by sorry
