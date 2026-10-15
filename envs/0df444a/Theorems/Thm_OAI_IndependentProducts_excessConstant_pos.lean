-- Prove2me | Theorems.Thm_OAI_IndependentProducts_excessConstant_pos
-- name    : OAI.IndependentProducts.excessConstant_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:07:46.756385+00:00
-- url     : https://prove2.me/theorems/48bbbcea-4e58-48ec-aed3-0761b79493c6
-- title:
--   Positivity of the Gaussian excess constant
-- statement:
--   Let $Z$ be a standard real Gaussian random variable, $Z\sim N(0,1)$. For $K\in\mathbb{R}$ the Gaussian excess constant is
--
--   $$c(K)=\frac{1}{16}\,\mathbb{E}\bigl[\max(|Z|-2K,\,0)\bigr]=\frac{1}{16}\int_{\mathbb{R}}\max(|x|-2K,\,0)\,\frac{e^{-x^2/2}}{\sqrt{2\pi}}\,dx .$$
--
--   For every real $K$ one has $c(K)>0$.
--
--   The constant $c(K)$ appears in the explicit lower bound for the averaged asymptotic midpoint modulus of the closed $L^1$ span of path products with exponential multipliers, where the modulus at $t>0$ is bounded below by $\tfrac{7t}{30}\,c(10/t)$; this lemma is exactly what makes that lower bound strictly positive.
--
--   **Formalization Note** In Lean `excessConstant K` is the real number $\tfrac1{16}\int\max(|x|-2K,0)\,d\gamma(x)$ with $\gamma$ = `gaussianReal 0 1`; no sign condition on $K$ is imposed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean#L40-L52

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι

theorem OAI.IndependentProducts.excessConstant_pos (K : ℝ) : 0 < excessConstant K := by sorry
