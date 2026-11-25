-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_bijOn_poleSecs_nsmul
-- name    : GlobalTheory.EffCartierData.bijOn_poleSecs_nsmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:11:03.552965+00:00
-- url     : https://prove2.me/theorems/08f02e17-55f7-4fe8-9265-b5fdf854f2ec
-- title:
--   Eff Cartier Data: bij On pole Secs nsmul
-- statement:
--   The Eff Cartier Data construction uses the bij On pole Secs nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L746-L749
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L746-L749

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

theorem GlobalTheory.EffCartierData.bijOn_poleSecs_nsmul (n : ℕ) (V : X.Opens) [Nonempty V] :
    Set.BijOn (ratOf (D.nsmul n).isLB_lb (D.nsmul n).canonical V) (secOn (D.nsmul n).lb V)
      (D.poleSecs n V) := by sorry
