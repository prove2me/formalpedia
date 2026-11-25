-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_mul_mem_poleSecs
-- name    : GlobalTheory.EffCartierData.mul_mem_poleSecs
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:53.574253+00:00
-- url     : https://prove2.me/theorems/e4185194-ffdb-40e8-bbf2-1cd22716ab87
-- title:
--   Eff Cartier Data: mul mem pole Secs
-- statement:
--   The Eff Cartier Data construction uses the mul mem pole Secs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L738-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L738-L744

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
variable [IsIntegral X]

theorem GlobalTheory.EffCartierData.mul_mem_poleSecs {m n : ℕ} {V : X.Opens} [Nonempty V] {h h' : X.functionField}
    (hh : h ∈ D.poleSecs m V) (hh' : h' ∈ D.poleSecs n V) : h * h' ∈ D.poleSecs (m + n) V := by sorry
