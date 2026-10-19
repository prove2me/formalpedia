-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_pairEntropyGap_le_quadratic
-- name    : OAI.LeanBlast.CourtadeKumar.pairEntropyGap_le_quadratic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:20:36.980905+00:00
-- url     : https://prove2.me/theorems/e7d6c472-0ed1-47df-9b00-f13b4068e0b2
-- title:
--   The pair entropy gap is at most $\log2\cdot b^2/(1-a^2)$
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$ and $h(v)=\log2-\psi(v)$. The pair entropy gap is $\Delta(a,b)=h(a)-\frac{h(a+b)+h(a-b)}{2}$. For real $a,b$ with $|a|+|b|<1$,
--   $$
--   \Delta(a,b)\le\log2\cdot\frac{b^2}{1-a^2}.
--   $$
--
--   The entropy lost when one coordinate of a function on the cube is averaged out is therefore at most $\log2$ times the normalized squared half-difference. This is the quadratic upper bound that sets the scale of the information-dissipation comparison.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PairEntropy.lean#L194-L210

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar

theorem OAI.LeanBlast.CourtadeKumar.pairEntropyGap_le_quadratic (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b ≤ ell * (b ^ 2 / (1 - a ^ 2)) := by sorry
