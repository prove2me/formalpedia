-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_rSecondDeriv_le_inv_ell
-- name    : OAI.LeanBlast.CourtadeKumar.rSecondDeriv_le_inv_ell
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:14:06.913141+00:00
-- url     : https://prove2.me/theorems/8db96779-ee70-43f4-9af4-088d35bafc98
-- title:
--   $r''\le1/\log2$ on $[0,\psi(1/5)]$
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$, a strictly increasing bijection $[0,1]\to[0,\log2]$ with inverse $\psi^{-1}$, and $h(v)=\log2-\psi(v)$. Let $r(s)=w\operatorname{artanh}w$ with $w=\psi^{-1}(s)$. For $s>0$ let $r'(s)=1+\frac{w}{(1-w^2)\operatorname{artanh}w}$ and $r''(s)=\frac{(1+w^2)\operatorname{artanh}w-w}{(1-w^2)^2(\operatorname{artanh}w)^3}$. For $s\le0$, $r'(s)=2$ and $r''(s)=\frac43$. Let $s_0=\psi(1/5)$. For every $s$ with $0\le s\le s_0$,
--   $$
--   r''(s)\le\frac{1}{\log2} .
--   $$
--
--   In the small range the curvature of $r$ stays below $1/\log2$. This justifies the linear extension of $r(s)-2s$ beyond $s_0$ used to define the auxiliary function $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CurvatureBounds.lean#L101-L116

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology

theorem OAI.LeanBlast.CourtadeKumar.rSecondDeriv_le_inv_ell {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s0) :
    rSecondDeriv s ≤ 1 / ell := by sorry
