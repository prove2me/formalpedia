-- Prove2me | Theorems.Thm_OAI_IndependentProducts_integral_excess_independent_copy
-- name    : OAI.IndependentProducts.integral_excess_independent_copy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:21:05.689548+00:00
-- url     : https://prove2.me/theorems/e68e96b8-0ad1-4d74-b73d-858ec55db090
-- title:
--   Replacing a variable by half its difference with an independent copy does not increase the expected excess
-- statement:
--   For $t,r,z\in\mathbb{R}$ define the excess function
--
--   $$\operatorname{exc}_{t,r}(z)=\max\bigl(t|z|-r,\ 0\bigr).$$
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $X:\Omega\to\mathbb{R}$ an integrable random variable, $t\ge0$ and $r\in\mathbb{R}$. Then, on $\Omega\times\Omega$ with the product measure $P\otimes P$,
--
--   $$\int_{\Omega\times\Omega}\operatorname{exc}_{t,r}\Bigl(\frac{X(\omega_1)-X(\omega_2)}{2}\Bigr)\,d(P\otimes P)(\omega_1,\omega_2)\ \le\ \int_{\Omega}\operatorname{exc}_{t,r}\bigl(X(\omega)\bigr)\,dP(\omega).$$
--
--   In probabilistic language: if $X'$ is an independent copy of $X$, then $\mathbb{E}\operatorname{exc}_{t,r}\bigl((X-X')/2\bigr)\le\mathbb{E}\operatorname{exc}_{t,r}(X)$. The excess function is the pointwise midpoint gain in $L^1$: for real $f,g$ and $t\ge0$ one has $\tfrac12\bigl(|f+tg|+|f-tg|\bigr)-|f|=\operatorname{exc}_{t,|f|}(g)$. The inequality lets lower bounds for the expected excess of a symmetrized variable, such as a Gaussian bilinear form obtained from squared Gaussians or a Laplace variable obtained from exponentials, be transferred back to the original variable.
--
--   **Formalization Note** The function $\operatorname{exc}_{t,r}$ is `excess t r`; the level $r$ may be negative, and only $t\ge0$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/GaussianMoments.lean#L143-L160

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι

theorem OAI.IndependentProducts.integral_excess_independent_copy {Ω : Type uΩ} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (∫ z : Ω × Ω, excess t r ((X z.1 - X z.2) / 2) ∂P.prod P) ≤
      ∫ ω, excess t r (X ω) ∂P := by sorry
