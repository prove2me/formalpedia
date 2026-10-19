-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_normalizedEntropy_actual
-- name    : OAI.LeanBlast.CourtadeKumar.normalizedEntropy_actual
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:04:39.613705+00:00
-- url     : https://prove2.me/theorems/9c31d549-3f9a-43bc-a7ea-66c8f23ee7d6
-- title:
--   Normalized entropy at joining coordinates
-- statement:
--   Let $b(z)=(e^z-1)^{-1}$ and, with $u=b(z)$, $v=b(w)$, $n=1+u+v$, let
--   $$
--   \mathcal N(z,w)=n\log n-\tfrac12\bigl((u+1)\log(u+1)+u\log u+(v+1)\log(v+1)+v\log v\bigr)
--   $$
--   be the normalized entropy, and $\partial_z\mathcal N$ its partial derivative in $z$. For $-1<y<x<1$ let $Z=\log\frac{1+x}{1+y}$ and $W=\log\frac{1-y}{1-x}$. Then
--   $$
--   \mathcal N(Z,W)=\frac{h(x)+h(y)}{x-y},
--   $$
--   where $h(v)$ is the entropy in nats of a random sign with mean $v$.
--
--   So at the joining coordinates the normalized entropy recovers the entropies of the two endpoints, per unit of separation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Canonical.lean#L441-L469

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology

theorem OAI.LeanBlast.CourtadeKumar.normalizedEntropy_actual {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1)
    (hxy : y < x) :
    normalizedEntropy (joiningZ x y) (joiningW x y) = (entropy x + entropy y)/(x-y) := by sorry
