-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_K_pos
-- name    : OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:18:26.020038+00:00
-- url     : https://prove2.me/theorems/ae5f841c-6019-4519-8d2f-52f7f789bd5b
-- title:
--   The modified gap function $K$ is differentiable at every $s>0$
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$, a strictly increasing bijection $[0,1]\to[0,\log2]$ with inverse $\psi^{-1}$, and $h(v)=\log2-\psi(v)$. Let $r(s)=w\operatorname{artanh}w$ with $w=\psi^{-1}(s)$. For $s>0$ let $r'(s)=1+\frac{w}{(1-w^2)\operatorname{artanh}w}$ and $r''(s)=\frac{(1+w^2)\operatorname{artanh}w-w}{(1-w^2)^2(\operatorname{artanh}w)^3}$. For $s\le0$, $r'(s)=2$ and $r''(s)=\frac43$. Let $s_0=\psi(1/5)$ and
--   $$
--   K(s)=\begin{cases}0,&s\le0,\\ r(s)-2s,&0<s\le s_0,\\ r(s_0)-2s_0+(r'(s_0)-2)(s-s_0),&s>s_0,\end{cases}
--   $$
--   with $K'(s)$ the corresponding piecewise derivative ($0$, $r'(s)-2$, $r'(s_0)-2$). Then for every $s>0$, $K$ is differentiable at $s$ with derivative $K'(s)$.
--
--   $K$ is the gap $r(s)-2s$ continued by its tangent line beyond $s_0$. The gluing is $C^1$, so $K$ can be used in calculus arguments on all of $(0,\infty)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/KRegularity.lean#L65-L96

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

theorem OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_pos {s : ℝ} (hs : 0 < s) : HasDerivAt K (KDeriv s) s := by sorry
