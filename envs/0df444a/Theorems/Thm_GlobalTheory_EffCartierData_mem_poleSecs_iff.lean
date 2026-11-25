-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_mem_poleSecs_iff
-- name    : GlobalTheory.EffCartierData.mem_poleSecs_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:21:07.005596+00:00
-- url     : https://prove2.me/theorems/87729130-faf2-5739-83c5-06c26239a408
-- title:
--   Eff Cartier Data: mem pole Secs iff
-- statement:
--   The Eff Cartier Data construction uses the mem pole Secs iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L698-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L698-L703

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

theorem GlobalTheory.EffCartierData.mem_poleSecs_iff (n : ℕ) (V : X.Opens) [Nonempty V] (h : X.functionField) :
    h ∈ D.poleSecs n V ↔ ∀ (i : D.ι) [Nonempty (V ⊓ D.U i : X.Opens)], ∃ a : Γ(X, V ⊓ D.U i),
      (X.germToFunctionField _).hom a =
        (X.germToFunctionField (V ⊓ D.U i)).hom (resG X inf_le_right (D.f i)) ^ n * h := by sorry
