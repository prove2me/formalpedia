-- Prove2me | Theorems.Thm_OAI_SoftChannel204_thinning_hard_bound
-- name    : OAI.SoftChannel204.thinning_hard_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:09:03.423212+00:00
-- url     : https://prove2.me/theorems/c184117b-50cd-4fe0-b22e-24cb6da20c6d
-- title:
--   An algebraic bound for the clipped kernel
-- statement:
--   Let $c_\beta(v)=\max(v-\beta,0)/v^2$. Let $0\le x<1$, $0<u\le1$, $\beta\le1$ with $\frac{4x}{3+x}\le\beta$, and suppose $1-\beta<c_\beta(u)$. Then
--   $$
--   \Bigl((1+x)\,c_\beta(u)-x(1-\beta)\Bigr)\cdot\frac{4x+(1-x)u}{(1-x)(1+x)}\le\frac32 .
--   $$
--
--   It is the hard case of the derivative bound in the thinning estimate, where the clipped kernel at $u$ exceeds its value $1-\beta$ at $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Thinning.lean#L174-L231

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

theorem OAI.SoftChannel204.thinning_hard_bound {x u β : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hβ1 : β ≤ 1)
    (hcut : 4 * x / (3 + x) ≤ β) (hh : 1 - β < clipKernel β u) :
    ((1 + x) * clipKernel β u - x * (1 - β)) *
      ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) ≤ 3 / 2 := by sorry
