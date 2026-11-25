-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_poleSecs_congr
-- name    : GlobalTheory.EffCartierData.poleSecs_congr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:53.655913+00:00
-- url     : https://prove2.me/theorems/c2d250f1-7af7-4364-bc90-60ccc2818c85
-- title:
--   Eff Cartier Data: pole Secs congr
-- statement:
--   The Eff Cartier Data construction uses the pole Secs congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L713-L717
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L713-L717

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
variable [IsIntegral X]

theorem GlobalTheory.EffCartierData.poleSecs_congr (h : D.idealSheaf = D'.idealSheaf) (n : ℕ) (V : X.Opens) [Nonempty V] :
    D.poleSecs n V = D'.poleSecs n V := by sorry
