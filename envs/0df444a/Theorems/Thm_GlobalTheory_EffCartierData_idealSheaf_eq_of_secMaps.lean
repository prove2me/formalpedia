-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_idealSheaf_eq_of_secMaps
-- name    : GlobalTheory.EffCartierData.idealSheaf_eq_of_secMaps
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:37.792352+00:00
-- url     : https://prove2.me/theorems/9534efc0-726f-5c98-bc3d-e0fc33f69a2d
-- title:
--   Eff Cartier Data: ideal Sheaf eq of sec Maps
-- statement:
--   The Eff Cartier Data construction uses the ideal Sheaf eq of sec Maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L307-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L307-L317

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

theorem GlobalTheory.EffCartierData.idealSheaf_eq_of_secMaps {w : LB.Iso D.lb D'.lb}
    (hw : SecMaps w D.canonical D'.canonical) : D.idealSheaf = D'.idealSheaf := by sorry
