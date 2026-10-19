-- Prove2me | Theorems.Thm_OAI_SoftChannel204_thinning_derivative_product
-- name    : OAI.SoftChannel204.thinning_derivative_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:10:36.130616+00:00
-- url     : https://prove2.me/theorems/2145d35d-0fa5-408b-98c9-c6b547222a94
-- title:
--   Derivative bound along a thinning path
-- statement:
--   Let $c_\beta(v)=\max(v-\beta,0)/v^2$. Let $0\le x<1$, $1\le a\le1+x$, $0\le s<\frac{1-x}{1+x}$, $\beta\le1$ with $\frac{4x}{3+x}\le\beta$. Put $u=2-a(1+s)$ and $v=u+s$. Then
--   $$
--   \bigl(a\,c_\beta(u)-(a-1)\,c_\beta(v)\bigr)\Bigl(\frac{1+x}{1-x}-s\Bigr)\le\frac32 .
--   $$
--
--   This bounds the derivative of the clipped integral along the path used in the thinning estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Thinning.lean#L233-L316

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

theorem OAI.SoftChannel204.thinning_derivative_product {x a s β : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (ha1 : 1 ≤ a) (hap : a ≤ 1 + x) (hs0 : 0 ≤ s)
    (hsg : s < (1 - x) / (1 + x)) (hβ1 : β ≤ 1)
    (hcut : 4 * x / (3 + x) ≤ β) :
    let u := 2 - a * (1 + s)
    let v := u + s
    (a * clipKernel β u - (a - 1) * clipKernel β v) *
      ((1 + x) / (1 - x) - s) ≤ 3 / 2 := by sorry
