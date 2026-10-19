-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_r_psi
-- name    : OAI.LeanBlast.CourtadeKumar.r_psi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:02:38.042691+00:00
-- url     : https://prove2.me/theorems/f9481678-9390-44bb-9433-be2aaa8dae04
-- title:
--   The function $r$ evaluated at $\psi(u)$ equals $u\operatorname{artanh}u$
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$, a strictly increasing bijection $[0,1]\to[0,\log2]$ with inverse $\psi^{-1}$, and $h(v)=\log2-\psi(v)$. Let $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$. Then for every $u\in(-1,1)$,
--   $$
--   r\bigl(\psi(u)\bigr)=u\operatorname{artanh}u .
--   $$
--
--   This expresses the dissipation weight $u\operatorname{artanh}u$ as a function of the entropy-type quantity $\psi(u)$. It is the identity that turns the dissipation inequality into a one-variable comparison.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/InverseScalars.lean#L139-L151

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology

theorem OAI.LeanBlast.CourtadeKumar.r_psi {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    r (psi u) = u * Real.artanh u := by sorry
