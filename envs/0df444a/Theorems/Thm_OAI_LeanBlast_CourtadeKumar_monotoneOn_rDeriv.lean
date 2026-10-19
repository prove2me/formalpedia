-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_monotoneOn_rDeriv
-- name    : OAI.LeanBlast.CourtadeKumar.monotoneOn_rDeriv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:06:49.511861+00:00
-- url     : https://prove2.me/theorems/c4b0e046-cbd3-4698-939e-131be952154d
-- title:
--   $r'$ is nondecreasing on $[0,\log2)$
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$, a strictly increasing bijection $[0,1]\to[0,\log2]$ with inverse $\psi^{-1}$, and $h(v)=\log2-\psi(v)$. Let $r(s)=w\operatorname{artanh}w$ with $w=\psi^{-1}(s)$. For $s>0$ let $r'(s)=1+\frac{w}{(1-w^2)\operatorname{artanh}w}$ and $r''(s)=\frac{(1+w^2)\operatorname{artanh}w-w}{(1-w^2)^2(\operatorname{artanh}w)^3}$. For $s\le0$, $r'(s)=2$ and $r''(s)=\frac43$. Then $r'$ is nondecreasing on $[0,\log2)$:
--   $$
--   0\le s\le t<\log2\ \Longrightarrow\ r'(s)\le r'(t).
--   $$
--
--   Equivalently, $r$ is convex on $[0,\log2)$, which is one of the key shape properties behind the information inequality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/InverseRegularity.lean#L169-L181

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology

theorem OAI.LeanBlast.CourtadeKumar.monotoneOn_rDeriv : MonotoneOn rDeriv (Ico 0 ell) := by sorry
