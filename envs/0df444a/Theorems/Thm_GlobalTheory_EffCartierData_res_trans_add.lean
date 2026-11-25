-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_res_trans_add
-- name    : GlobalTheory.EffCartierData.res_trans_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:24.597798+00:00
-- url     : https://prove2.me/theorems/4ddfcd5d-6346-4f33-8ba4-cb9339e6ca35
-- title:
--   Eff Cartier Data: res trans add
-- statement:
--   The Eff Cartier Data construction uses the res trans add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L546-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L546-L556

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

theorem GlobalTheory.EffCartierData.res_trans_add (p q : D.ι × D'.ι) {W : X.Opens} (hp : W ≤ D.U p.1 ⊓ D'.U p.2)
    (hq : W ≤ D.U q.1 ⊓ D'.U q.2) :
    res (le_inf hp hq) ((D.add D').trans p q) =
      res (le_inf (hp.trans inf_le_left) (hq.trans inf_le_left)) (D.trans p.1 q.1) *
        res (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)) (D'.trans p.2 q.2) := by sorry
