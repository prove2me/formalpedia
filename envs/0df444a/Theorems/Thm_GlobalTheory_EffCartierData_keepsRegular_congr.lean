-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_keepsRegular_congr
-- name    : GlobalTheory.EffCartierData.keepsRegular_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:28.294471+00:00
-- url     : https://prove2.me/theorems/26873167-3170-4b86-b2ed-9ed84ac89afd
-- title:
--   Eff Cartier Data: keeps Regular congr
-- statement:
--   The Eff Cartier Data construction uses the keeps Regular congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L439-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L439-L441

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

theorem GlobalTheory.EffCartierData.keepsRegular_congr (h : D.idealSheaf = D'.idealSheaf) (φ : Y ⟶ X) :
    D.KeepsRegular φ ↔ D'.KeepsRegular φ := by sorry
