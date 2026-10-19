-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_comparison_middle_regime
-- name    : OAI.LeanBlast.CourtadeKumar.comparison_middle_regime
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:01:45.818592+00:00
-- url     : https://prove2.me/theorems/750345e1-3a5a-4820-b5e7-c02d6558efec
-- title:
--   An algebraic comparison step for the middle range of correlations
-- statement:
--   Let $m,u,B,P,S,v$ be real numbers with
--   $$
--   0\le B\le m^2\Bigl(\log2-\frac12\Bigr),\qquad \frac{u^2}{2}\le P,\qquad S\le(1-m^2)P+B(1-v),\qquad 1-v\le\frac52u^2 .
--   $$
--   Then $S\le P$.
--
--   In the middle regime of the noise parameter, a correction term $B(1-v)$ is absorbed into the main term $m^2P$. This works because $\frac52(\log2-\frac12)\le\frac12$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/ComparisonEstimates.lean#L130-L149

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set

theorem OAI.LeanBlast.CourtadeKumar.comparison_middle_regime (m u B P S v : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ m ^ 2 * (ell - 1 / 2))
    (hP : u ^ 2 / 2 ≤ P)
    (hS : S ≤ (1 - m ^ 2) * P + B * (1 - v))
    (hv : 1 - v ≤ (5 / 2 : ℝ) * u ^ 2) : S ≤ P := by sorry
