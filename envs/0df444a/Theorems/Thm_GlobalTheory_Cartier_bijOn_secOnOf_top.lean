-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_bijOn_secOnOf_top
-- name    : GlobalTheory.Cartier.bijOn_secOnOf_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:10:52.425848+00:00
-- url     : https://prove2.me/theorems/b1277458-159a-45d1-a5fa-d82f2ce48543
-- title:
--   Cartier: bij On sec On Of top
-- statement:
--   The Cartier construction uses the bij On sec On Of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L26-L38

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
open GlobalTheory.Cartier
variable {X : Scheme.{0}}

theorem GlobalTheory.Cartier.bijOn_secOnOf_top (L : LB X) :
    Set.BijOn (fun t : L.Sec => secOnOf t ⊤) Set.univ (secOn L ⊤) := by sorry
