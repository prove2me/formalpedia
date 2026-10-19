-- Prove2me | Theorems.Thm_OAI_SoftChannel204_thinning_interval_aux
-- name    : OAI.SoftChannel204.thinning_interval_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:11:24.1354+00:00
-- url     : https://prove2.me/theorems/d802903b-2146-4819-89de-c8399fac1877
-- title:
--   Integral of the clipped kernel over a short window
-- statement:
--   Let $c_\beta(v)=\max(v-\beta,0)/v^2$ be the clipped kernel. Let $0\le x<1$, $\beta\le1$ with $\frac{4x}{3+x}\le\beta$, $0\le z<\gamma$ where $\gamma=\frac{1-x}{1+x}$, and $1-x-(1+x)z\le u\le1-z$. Then
--   $$
--   \int_u^{u+z}c_\beta(v)\,dv\le-\frac32\log(1-\gamma z).
--   $$
--
--   The window length $z$ is paid for logarithmically, uniformly in its position $u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Thinning.lean#L343-L433

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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
import Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
import Definitions.Def_OAI_InformationTheory_SoftChannel_Thinning

open OAI OAI.SoftChannel204
open Set
open MeasureTheory

theorem OAI.SoftChannel204.thinning_interval_aux {x β u z : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hβ1 : β ≤ 1) (hcut : 4 * x / (3 + x) ≤ β)
    (hz0 : 0 ≤ z) (hzg : z < (1 - x) / (1 + x))
    (hulo : 1 - x - (1 + x) * z ≤ u) (huhi : u ≤ 1 - z) :
    (∫ v in u..u+z, clipKernel β v) ≤
      -(3 / 2 : ℝ) * Real.log (1 - ((1 - x) / (1 + x)) * z) := by sorry
