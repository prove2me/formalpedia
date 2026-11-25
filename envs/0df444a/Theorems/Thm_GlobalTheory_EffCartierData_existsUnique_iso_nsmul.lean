-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_existsUnique_iso_nsmul
-- name    : GlobalTheory.EffCartierData.existsUnique_iso_nsmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:37.306439+00:00
-- url     : https://prove2.me/theorems/893585df-76e1-435e-b892-2681a6f3d84c
-- title:
--   Eff Cartier Data: exists Unique iso nsmul
-- statement:
--   The Eff Cartier Data construction uses the exists Unique iso nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L660-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L660-L669

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

theorem GlobalTheory.EffCartierData.existsUnique_iso_nsmul (n : ℕ) :
    ∃! w : LB.Iso (D.nsmul n).lb (lbPow D.lb n),
      w.IsGen ∧ SecMaps w (D.nsmul n).canonical (secPow D.canonical n) := by sorry
