-- Prove2me | Theorems.Thm_OAI_IndependentProducts_integral_complex_exp_exponentialLaw
-- name    : OAI.IndependentProducts.integral_complex_exp_exponentialLaw
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:53:14.524471+00:00
-- url     : https://prove2.me/theorems/f890ab2b-1b49-4864-9335-ba1e351ff501
-- title:
--   Complex moment generating function of the standard exponential law
-- statement:
--   Let $\mathrm{Exp}(1)$ denote the standard exponential distribution, i.e. the Borel probability measure on $\mathbb R$ with density $e^{-x}$ on $(0,\infty)$ and no mass on $(-\infty,0)$. For every complex number $z$ with $\operatorname{Re} z<1$,
--
--   $$
--   \int_{\mathbb R} e^{zx}\,d\,\mathrm{Exp}(1)(x)\;=\;\frac{1}{1-z}.
--   $$
--
--   This is the complex moment generating function of the exponential law on its half-plane of convergence. It contains both the Laplace transform ($z=-q$ with $q\ge 0$, giving $1/(1+q)$) and the characteristic function ($z=iq$ with $q$ real, giving $1/(1-iq)$); in the product-space application it is used to compute characteristic functions of linear combinations of independent exponential variables.
--
--   **Formalization Note** The measure is `exponentialLaw`, defined as Mathlib's `expMeasure 1`; the left-hand side is the Bochner integral of the complex-valued function $x\mapsto e^{zx}$, with $x$ coerced from $\mathbb R$ to $\mathbb C$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ExponentialLaw.lean#L67-L81

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialLaw

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uE

theorem OAI.IndependentProducts.integral_complex_exp_exponentialLaw (z : ℂ) (hz : z.re < 1) :
    (∫ x : ℝ, Complex.exp (z * x) ∂exponentialLaw) = 1 / (1 - z) := by sorry
