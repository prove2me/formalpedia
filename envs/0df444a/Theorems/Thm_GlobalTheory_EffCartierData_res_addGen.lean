-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_res_addGen
-- name    : GlobalTheory.EffCartierData.res_addGen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:18.712119+00:00
-- url     : https://prove2.me/theorems/ac729aa1-55f3-4cf1-8f59-ec549ec28915
-- title:
--   Eff Cartier Data: res add Gen
-- statement:
--   The Eff Cartier Data construction uses the res add Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L565-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L565-L573

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

theorem GlobalTheory.EffCartierData.res_addGen (i j : D.ι) (i' j' : D'.ι) {W : X.Opens}
    (h : W ≤ D.U i ⊓ D'.U i' ⊓ D.U j ⊓ D'.U j') :
    res h ((D.addGen D').s (((i, i'), j), j')) =
      res (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
        (h.trans (inf_le_left.trans inf_le_right))) (D.trans i j) *
      res (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
        (h.trans inf_le_right)) (D'.trans i' j') := by sorry
