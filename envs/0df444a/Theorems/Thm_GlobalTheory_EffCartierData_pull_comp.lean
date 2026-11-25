-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_pull_comp
-- name    : GlobalTheory.EffCartierData.pull_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:19.016206+00:00
-- url     : https://prove2.me/theorems/dcaf5019-3427-44c2-9a17-2f2c08d0d03c
-- title:
--   Eff Cartier Data: pull comp
-- statement:
--   The Eff Cartier Data construction uses the pull comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L503-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L503-L505

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

theorem GlobalTheory.EffCartierData.pull_comp (φ : Y ⟶ X) (h : D.KeepsRegular φ) (ψ : Z ⟶ Y)
    (h' : (D.pull φ h).KeepsRegular ψ) :
    D.pull (ψ ≫ φ) ((D.keepsRegular_comp_iff φ h ψ).2 h') = (D.pull φ h).pull ψ h' := by sorry
