-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Translation_translation_derivative
-- name    : OAI.GaussianPropeller.Translation.translation_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:01:27.060984+00:00
-- url     : https://prove2.me/theorems/af7a51d3-610b-4f08-80c3-e4f788268309
-- title:
--   Derivative of the Gaussian measure of a translated set
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on $\mathbb R^\iota$, $A$ a measurable set and $h$ a vector. The function $u\mapsto\gamma(A+uh)$, the measure of $A$ under the image of $\gamma$ by $x\mapsto x-uh$, is differentiable at $u=0$ with
--   $$
--   \frac{d}{du}\Big|_{u=0}\gamma(A+uh)=-\Bigl\langle h,\int_Ax\,d\gamma(x)\Bigr\rangle .
--   $$
--
--   So moving a set in direction $h$ changes its mass at the rate given by its Gaussian centroid.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Translation.lean#L168-L199

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Translation
universe uE uX uY uι
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

theorem OAI.GaussianPropeller.Translation.translation_derivative {ι : Type uι} [Fintype ι]
    (h : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) :
    HasDerivAt (fun u : ℝ =>
      ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x-u•h)).real A)
      (-⟪h, ∫ x in A, x ∂stdGaussian (EuclideanSpace ℝ ι)⟫) 0 := by sorry
