-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_normalizedEntropy_tangent
-- name    : OAI.LeanBlast.CourtadeKumar.normalizedEntropy_tangent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:03:57.811401+00:00
-- url     : https://prove2.me/theorems/423f2d57-54fb-4ca1-9057-de7b5dbbc9de
-- title:
--   Tangent plane inequality for the normalized entropy
-- statement:
--   Let $b(z)=(e^z-1)^{-1}$ and, with $u=b(z)$, $v=b(w)$, $n=1+u+v$, let
--   $$
--   \mathcal N(z,w)=n\log n-\tfrac12\bigl((u+1)\log(u+1)+u\log u+(v+1)\log(v+1)+v\log v\bigr)
--   $$
--   be the normalized entropy, and $\partial_z\mathcal N$ its partial derivative in $z$. For $z,w,Z,W>0$,
--   $$
--   \mathcal N(z,w)+\partial_z\mathcal N(z,w)\,(Z-z)+\partial_w\mathcal N(z,w)\,(W-w)\le\mathcal N(Z,W).
--   $$
--
--   So $\mathcal N$ lies above its tangent planes on the positive quadrant, as a convex function does.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Canonical.lean#L277-L298

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

theorem OAI.LeanBlast.CourtadeKumar.normalizedEntropy_tangent {z w Z W : ℝ}
    (hz : 0 < z) (hw : 0 < w) (hZ : 0 < Z) (hW : 0 < W) :
    normalizedEntropy z w + normalizedEntropyDz z w * (Z-z) +
      normalizedEntropyDz w z * (W-w) ≤ normalizedEntropy Z W := by sorry
