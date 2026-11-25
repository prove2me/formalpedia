-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_addGen_canonical
-- name    : GlobalTheory.EffCartierData.addGen_canonical
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:24.41656+00:00
-- url     : https://prove2.me/theorems/7986356a-d5c5-4613-a410-21b1be388f99
-- title:
--   Eff Cartier Data: add Gen canonical
-- statement:
--   The Eff Cartier Data construction uses the add Gen canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L575-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L575-L584

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

theorem GlobalTheory.EffCartierData.addGen_canonical (i j : D.ι) (i' j' : D'.ι) {W : X.Opens}
    (h : W ≤ D.U i ⊓ D'.U i' ⊓ D.U j ⊓ D'.U j') :
    resG X (h.trans (inf_le_left.trans inf_le_left)) ((D.add D').canonical.f (i, i')) =
      (res h ((D.addGen D').s (((i, i'), j), j')) : Γ(X, W)ˣ) *
        (resG X (h.trans (inf_le_left.trans inf_le_right)) (D.canonical.f j) *
          resG X (h.trans inf_le_right) (D'.canonical.f j')) := by sorry
