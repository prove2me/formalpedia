-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_bijOn_poleSecs_one
-- name    : GlobalTheory.EffCartierData.bijOn_poleSecs_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:18:28.967886+00:00
-- url     : https://prove2.me/theorems/b5daa03b-e543-5ff1-bc9f-afd10be79e7c
-- title:
--   Eff Cartier Data: bij On pole Secs one
-- statement:
--   The Eff Cartier Data construction uses the bij On pole Secs one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L771-L775
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L771-L775

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

theorem GlobalTheory.EffCartierData.bijOn_poleSecs_one (V : X.Opens) [Nonempty V] :
    Set.BijOn (ratOf D.isLB_lb D.canonical V) (secOn D.lb V) (D.poleSecs 1 V) := by sorry
