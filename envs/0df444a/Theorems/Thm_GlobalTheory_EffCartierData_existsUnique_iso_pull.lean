-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_existsUnique_iso_pull
-- name    : GlobalTheory.EffCartierData.existsUnique_iso_pull
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:30.779739+00:00
-- url     : https://prove2.me/theorems/e46c941e-2e5c-42a0-990c-71db48232db2
-- title:
--   Eff Cartier Data: exists Unique iso pull
-- statement:
--   The Eff Cartier Data construction uses the exists Unique iso pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L487-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L487-L495

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

theorem GlobalTheory.EffCartierData.existsUnique_iso_pull (φ : Y ⟶ X) (h : D.KeepsRegular φ) :
    ∃! w : LB.Iso (D.pull φ h).lb (D.lb.pull φ),
      w.IsGen ∧ SecMaps w (D.pull φ h).canonical (secPull D.canonical φ) := by sorry
