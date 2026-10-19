-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_K_zero_of_right_derivative
-- name    : OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_zero_of_right_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:19:04.981261+00:00
-- url     : https://prove2.me/theorems/730e0f9c-836f-455e-af01-e2b1c1ec913c
-- title:
--   If $r(s)-2s$ has right derivative $0$ at $0$, then $K'(0)=0$
-- statement:
--   Let $g(s)=r(s)-2s$, where $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$. Let $K$ be $0$ on $(-\infty,0]$, equal to $g$ on $(0,s_0]$ with $s_0=\psi(1/5)$, and linear beyond. Assume that $g$, restricted to $[0,\infty)$, has derivative $0$ at $0$:
--   $$
--   \lim_{s\to0^+}\frac{g(s)-g(0)}{s}=0 .
--   $$
--   Then $K$ is differentiable at $0$ with $K'(0)=0$.
--
--   Combined with differentiability at positive points, this makes $K$ differentiable on all of $\mathbb{R}$. The hypothesis is the endpoint behaviour $r'(0^+)=2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/KRegularity.lean#L98-L112

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology

theorem OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_zero_of_right_derivative
    (hzero : HasDerivWithinAt rGap 0 (Ici 0) 0) : HasDerivAt K 0 0 := by sorry
