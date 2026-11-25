-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_associated_of_idealSheaf_eq
-- name    : GlobalTheory.EffCartierData.associated_of_idealSheaf_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:24.388886+00:00
-- url     : https://prove2.me/theorems/c853e825-1502-52c1-959e-ba94860fffff
-- title:
--   Eff Cartier Data: associated of ideal Sheaf eq
-- statement:
--   The Eff Cartier Data construction uses the associated of ideal Sheaf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L294-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L294-L298

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

theorem GlobalTheory.EffCartierData.associated_of_idealSheaf_eq (h : D.idealSheaf = D'.idealSheaf) (p : D'.ι) (q : D.ι) :
    Associated (resG X (inf_le_right : D'.U p ⊓ D.U q ≤ D.U q) (D.f q))
      (resG X (inf_le_left : D'.U p ⊓ D.U q ≤ D'.U p) (D'.f p)) := by sorry
