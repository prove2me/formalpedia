-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_SmoothGaussian_weighted_interval_bounds
-- name    : OAI.SquareRootDegree.SmoothGaussian.weighted_interval_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:48.37859+00:00
-- url     : https://prove2.me/theorems/760a9cb4-1e00-4266-910e-82086c326e97
-- title:
--   Mean and variance of a nonnegative weight supported in $[a-h,a+h]$
-- statement:
--   Let $\mu$ be a measure on $\mathbb R$ and $w:\mathbb R\to\mathbb R$ a weight, and define its mass, mean and variance
--   $$M(w)=\int w\,d\mu,\qquad m(w)=\frac{1}{M(w)}\int x\,w(x)\,d\mu(x),\qquad V(w)=\frac{1}{M(w)}\int x^2w(x)\,d\mu(x)-m(w)^2 .$$
--   Let $a\in\mathbb R$ and $h\ge0$, and assume:
--   1. $w(x)\ge0$ for all $x$;
--   2. $w$ vanishes outside $[a-h,a+h]$, i.e. $w(x)\neq0$ implies $|x-a|\le h$;
--   3. $w$, $x\mapsto x\,w(x)$ and $x\mapsto x^2w(x)$ are $\mu$-integrable;
--   4. $M(w)>0$.
--
--   Then
--
--   $$
--   |m(w)-a|\le h,\qquad 0\le V(w),\qquad V(w)\le h^2 .
--   $$
--
--   In other words, the probability measure $w\,d\mu/M(w)$, which lives on $[a-h,a+h]$, has its mean within $h$ of the centre $a$ and variance between $0$ and $h^2$. Applied to a narrow tent and the Gaussian measure, this shows that a soft interval test of half-width $h$ around $a$ has conditional mean close to $a$ and conditional variance of order $h^2$.
--
--   **Formalization Note** $M$, $m$ and $V$ are `mass μ w`, `mean μ w` and `variance μ w`. The measure $\mu$ is arbitrary (not necessarily finite), and positivity of the mass is assumed explicitly, so no division-by-zero convention is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/SmoothGaussian.lean#L151-L203

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.SmoothGaussian
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

theorem OAI.SquareRootDegree.SmoothGaussian.weighted_interval_bounds (μ : Measure ℝ) (w : ℝ → ℝ) {a h : ℝ}
    (hh : 0 ≤ h) (hw : ∀ x, 0 ≤ w x)
    (hs : ∀ x, w x ≠ 0 → |x-a| ≤ h)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x*x) μ)
    (h2 : Integrable (fun x => w x*x^2) μ) (hb : 0 < mass μ w) :
    |mean μ w-a| ≤ h ∧ 0 ≤ variance μ w ∧ variance μ w ≤ h^2 := by sorry
