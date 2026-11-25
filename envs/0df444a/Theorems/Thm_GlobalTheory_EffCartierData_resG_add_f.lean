-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_resG_add_f
-- name    : GlobalTheory.EffCartierData.resG_add_f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:22.334594+00:00
-- url     : https://prove2.me/theorems/d69c04c6-f5ac-4738-a052-31106573261b
-- title:
--   Eff Cartier Data: res G add f
-- statement:
--   The Eff Cartier Data construction uses the res G add f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L529-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L529-L533

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

theorem GlobalTheory.EffCartierData.resG_add_f (i : D.ι) (j : D'.ι) {W : X.Opens} (h : W ≤ D.U i ⊓ D'.U j) :
    resG X h ((D.add D').f (i, j)) =
      resG X (h.trans inf_le_left) (D.f i) * resG X (h.trans inf_le_right) (D'.f j) := by sorry
