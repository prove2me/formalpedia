-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Translation_stdGaussian_map_add
-- name    : OAI.GaussianPropeller.Translation.stdGaussian_map_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:00:40.308992+00:00
-- url     : https://prove2.me/theorems/6789c5d1-f1df-4d05-8c10-8a1f8584b8c5
-- title:
--   Translates of the standard Gaussian measure
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on $\mathbb R^\iota$ and $v\in\mathbb R^\iota$. The image of $\gamma$ under $x\mapsto x+v$ has density with respect to $\gamma$:
--   $$
--   d\bigl(\tau_v\bigr)_*\gamma(x)=e^{\langle v,x\rangle-|v|^2/2}\,d\gamma(x).
--   $$
--
--   This is the Cameron–Martin formula in finite dimensions; it converts translations of cells into exponential tilts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Translation.lean#L119-L136

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

theorem OAI.GaussianPropeller.Translation.stdGaussian_map_add {ι : Type uι} [Fintype ι]
    (v : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x+v) =
      (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (⟪v,x⟫-‖v‖^2/2))) := by sorry
