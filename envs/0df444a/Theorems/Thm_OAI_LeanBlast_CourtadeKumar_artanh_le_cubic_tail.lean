-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_artanh_le_cubic_tail
-- name    : OAI.LeanBlast.CourtadeKumar.artanh_le_cubic_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:07:53.525983+00:00
-- url     : https://prove2.me/theorems/af8c1a4b-77ec-46fe-bf42-2d7271ce0481
-- title:
--   $\operatorname{artanh}u\le u+\frac{u^3}{3(1-u^2)}$ for $0\le u<1$
-- statement:
--   For every $u\in[0,1)$,
--   $$
--   \operatorname{artanh}u\le u+\frac{u^3}{3(1-u^2)} .
--   $$
--
--   This is a cheap upper bound on $\operatorname{artanh}$, sharp to third order at $0$. It is used to bound the curvature of $r$ in the small range.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/SmallCurvatureAux.lean#L7-L34

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

theorem OAI.LeanBlast.CourtadeKumar.artanh_le_cubic_tail {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    Real.artanh u ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := by sorry
