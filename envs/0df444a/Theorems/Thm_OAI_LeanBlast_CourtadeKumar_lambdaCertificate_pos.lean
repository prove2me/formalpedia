-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_lambdaCertificate_pos
-- name    : OAI.LeanBlast.CourtadeKumar.lambdaCertificate_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:59:02.791006+00:00
-- url     : https://prove2.me/theorems/0a3f03bb-a75f-4813-a8fb-e26c2b4c4d8f
-- title:
--   The certificate polynomial $\Lambda$ is positive on $[0,1]$
-- statement:
--   Let
--   $$
--   \Lambda(b)=4-\tfrac52b-5b^2-\tfrac74b^3+\tfrac{56}{15}b^4+b^5+\tfrac{15}{14}b^6+\tfrac38b^7+\tfrac8{15}b^8 .
--   $$
--   Then $\Lambda(b)>0$ for every $b\in[0,1]$.
--
--   This positivity is one of the polynomial inequalities certified exactly, here via Bernstein coefficients on two subintervals. It feeds the perspective inequality in the curvature analysis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CurvatureCertificates.lean#L137-L151

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators

theorem OAI.LeanBlast.CourtadeKumar.lambdaCertificate_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < lambdaPolynomial b := by sorry
