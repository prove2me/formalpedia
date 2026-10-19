-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_convexOn_L
-- name    : OAI.LeanBlast.CourtadeKumar.convexOn_L
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:16:41.602809+00:00
-- url     : https://prove2.me/theorems/540e7265-e810-41f1-8c46-d1caedfde379
-- title:
--   The gap function $L(x)=r(\log2-x)-2(\log2-x)$ is convex on $(0,\infty)$
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$, a strictly increasing bijection $[0,1]\to[0,\log2]$ with inverse $\psi^{-1}$, and $h(v)=\log2-\psi(v)$. Let $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$, and define $L(x)=r(\log2-x)-2(\log2-x)$ for $0<x<\log2$ and $L(x)=0$ otherwise. Then $L$ is convex on $(0,\infty)$: for $x,y>0$ and $a,b\ge0$ with $a+b=1$,
--   $$
--   L(ax+by)\le a\,L(x)+b\,L(y).
--   $$
--
--   Convexity of $L$ allows Jensen's inequality to be applied to the dissipation–entropy comparison at each step of the induction on dimension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/LShape.lean#L32-L55

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set

theorem OAI.LeanBlast.CourtadeKumar.convexOn_L : ConvexOn ℝ (Ioi 0) L := by sorry
