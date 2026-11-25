-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_existsUnique_iso_of_idealSheaf_eq
-- name    : GlobalTheory.EffCartierData.existsUnique_iso_of_idealSheaf_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:56.815106+00:00
-- url     : https://prove2.me/theorems/dcd7d27c-20f6-4142-b32a-89300b0d7c0a
-- title:
--   Eff Cartier Data: exists Unique iso of ideal Sheaf eq
-- statement:
--   The Eff Cartier Data construction uses the exists Unique iso of ideal Sheaf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L300-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L300-L302

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

theorem GlobalTheory.EffCartierData.existsUnique_iso_of_idealSheaf_eq (h : D.idealSheaf = D'.idealSheaf) :
    ∃! w : LB.Iso D.lb D'.lb, w.IsGen ∧ SecMaps w D.canonical D'.canonical := by sorry
