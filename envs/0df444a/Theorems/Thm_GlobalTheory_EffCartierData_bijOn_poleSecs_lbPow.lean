-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_bijOn_poleSecs_lbPow
-- name    : GlobalTheory.EffCartierData.bijOn_poleSecs_lbPow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:32.981251+00:00
-- url     : https://prove2.me/theorems/7fcb514f-8e13-51be-bcc5-6a833220d545
-- title:
--   Eff Cartier Data: bij On pole Secs lb Pow
-- statement:
--   The Eff Cartier Data construction uses the bij On pole Secs lb Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L764-L769
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L764-L769

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_IsRegularSec_secPow

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

theorem GlobalTheory.EffCartierData.bijOn_poleSecs_lbPow (n : ℕ) (V : X.Opens) [Nonempty V] :
    Set.BijOn (ratOf (D.isLB_lbPow n) (secPow D.canonical n) V) (secOn (lbPow D.lb n) V)
      (D.poleSecs n V) := by sorry
