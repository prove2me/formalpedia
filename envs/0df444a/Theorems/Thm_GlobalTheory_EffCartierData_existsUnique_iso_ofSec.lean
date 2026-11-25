-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_existsUnique_iso_ofSec
-- name    : GlobalTheory.EffCartierData.existsUnique_iso_ofSec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:13.640277+00:00
-- url     : https://prove2.me/theorems/8f433b87-435b-444d-979f-07965faf1ca5
-- title:
--   Eff Cartier Data: exists Unique iso of Sec
-- statement:
--   The Eff Cartier Data construction uses the exists Unique iso of Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L357-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L357-L359

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

theorem GlobalTheory.EffCartierData.existsUnique_iso_ofSec {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    ∃! w : LB.Iso L (ofSec hL s hs).lb, w.IsGen ∧ SecMaps w s (ofSec hL s hs).canonical := by sorry
