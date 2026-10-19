-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_le_of_deriv_le_on_above_of_tendsto
-- name    : OAI.LeanBlast.CourtadeKumar.le_of_deriv_le_on_above_of_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:00:43.894627+00:00
-- url     : https://prove2.me/theorems/731af5cd-74dc-44fa-83d2-2d0875afcfec
-- title:
--   A comparison principle for differential inequalities from zero
-- statement:
--   Let $f,g$ be differentiable on $(0,\infty)$ with derivatives $f',g'$. Suppose that whenever $g(t)\le f(t)$ we have $f'(t)\le g'(t)$, and that $f$ and $g$ have the same limit $l$ as $t\to0^+$. Then
--   $$
--   f(t)\le g(t)\qquad\text{for all }t>0 .
--   $$
--
--   It is used to compare the information along the noise semigroup with the explicit soft-dictator curve.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Comparison.lean#L70-L91

import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem OAI.LeanBlast.CourtadeKumar.le_of_deriv_le_on_above_of_tendsto
    {f g f' g' : ℝ → ℝ} {l : ℝ}
    (hf : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hg : ∀ t, 0 < t → HasDerivAt g (g' t) t)
    (hderiv : ∀ t, 0 < t → g t ≤ f t → f' t ≤ g' t)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 l))
    (hg0 : Tendsto g (𝓝[>] 0) (𝓝 l)) :
    ∀ t, 0 < t → f t ≤ g t := by sorry
