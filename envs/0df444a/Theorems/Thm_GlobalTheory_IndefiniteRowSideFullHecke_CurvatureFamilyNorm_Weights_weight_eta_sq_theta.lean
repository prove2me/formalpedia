-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CurvatureFamilyNorm_Weights_weight_eta_sq_theta
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.weight_eta_sq_theta
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:55.417897+00:00
-- url     : https://prove2.me/theorems/df5d625f-1538-590a-8b11-c06a291fa148
-- title:
--   Weights: weight eta sq theta
-- statement:
--   The Weights construction uses the weight eta sq theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/CurvatureFamilyNorm.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/CurvatureFamilyNorm.lean#L97-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_CurvatureFamilyNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights
variable {X : Data E r} (w : Weights X)

theorem GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.weight_eta_sq_theta : (2 : ℤ) • w.wEt + (w.n₁ : ℤ) • w.twoG₁ = (2 * (w.n₁ : ℤ)) • w.L := by sorry
