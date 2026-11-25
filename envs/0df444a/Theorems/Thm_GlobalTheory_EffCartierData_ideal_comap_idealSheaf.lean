-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_ideal_comap_idealSheaf
-- name    : GlobalTheory.EffCartierData.ideal_comap_idealSheaf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:15.305531+00:00
-- url     : https://prove2.me/theorems/0d365228-dd3a-5a0b-9360-b3f4c006c404
-- title:
--   Eff Cartier Data: ideal comap ideal Sheaf
-- statement:
--   The Eff Cartier Data construction uses the ideal comap ideal Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L415-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L415-L419

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

theorem GlobalTheory.EffCartierData.ideal_comap_idealSheaf (φ : Y ⟶ X) (W : Y.affineOpens) (i : D.ι)
    (h : W.1 ≤ φ ⁻¹ᵁ D.U i) :
    (D.idealSheaf.comap φ).ideal W = Ideal.span {resG Y h ((φ.app (D.U i)).hom (D.f i))} := by sorry
