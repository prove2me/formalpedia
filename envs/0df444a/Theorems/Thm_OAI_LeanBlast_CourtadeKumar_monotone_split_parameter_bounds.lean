-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_monotone_split_parameter_bounds
-- name    : OAI.LeanBlast.CourtadeKumar.monotone_split_parameter_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:35:26.553195+00:00
-- url     : https://prove2.me/theorems/34cbca1d-c03a-4ac9-81a4-326f416b829b
-- title:
--   Range bounds for the normalized split parameters of a monotone function
-- statement:
--   Let $m,k,W\in\mathbb{R}$ with
--   $$
--   |m|<1,\qquad 0\le k<1-|m|,\qquad 0<W\le1-m^2,\qquad k\le W .
--   $$
--   Then, with $A=1-m^2$,
--   $$
--   0\le\frac{k^2}{A}<1,\qquad 0<\frac WA\le1,\qquad \frac{k^2}{A}\le\Bigl(\frac WA\Bigr)^2 .
--   $$
--
--   When a monotone function is split along a coordinate, these are the parameter ranges for the normalized squared half-difference $k^2/A$ and the normalized influence $W/A$. They make the one-variable curvature and $\lambda$-inequalities applicable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/MonotoneDissipation.lean#L118-L138

import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
open Set

theorem OAI.LeanBlast.CourtadeKumar.monotone_split_parameter_bounds {m k W : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W) :
    0 ≤ k ^ 2 / (1 - m ^ 2) ∧ k ^ 2 / (1 - m ^ 2) < 1 ∧
      0 < W / (1 - m ^ 2) ∧ W / (1 - m ^ 2) ≤ 1 ∧
      k ^ 2 / (1 - m ^ 2) ≤ (W / (1 - m ^ 2)) ^ 2 := by sorry
