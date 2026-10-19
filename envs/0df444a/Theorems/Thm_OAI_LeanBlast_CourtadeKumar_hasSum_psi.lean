-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasSum_psi
-- name    : OAI.LeanBlast.CourtadeKumar.hasSum_psi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:04:19.417256+00:00
-- url     : https://prove2.me/theorems/46d6fb8b-26f3-4cdd-bbe6-abdc6a63a7a6
-- title:
--   Power series of the entropy function: $\psi(v)=\sum_k\frac{v^{2k+2}}{(2k+1)(2k+2)}$
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$. For every real $v$ with $|v|<1$,
--   $$
--   \psi(v)=\sum_{k=0}^{\infty}\frac{v^{2k+2}}{(2k+1)(2k+2)},
--   $$
--   the series converging (as a `HasSum`).
--
--   All coefficients are positive, so polynomial truncations give lower bounds and explicit tail estimates give upper bounds. These are the polynomial certificates for the curvature inequalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/EntropySeries.lean#L54-L73

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
open Set Filter Finset
open scoped Topology BigOperators

theorem OAI.LeanBlast.CourtadeKumar.hasSum_psi {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by sorry
