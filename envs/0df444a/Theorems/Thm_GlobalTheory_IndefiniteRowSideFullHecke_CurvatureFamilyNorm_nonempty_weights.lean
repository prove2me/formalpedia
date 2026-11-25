-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CurvatureFamilyNorm_nonempty_weights
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.nonempty_weights
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:48.686881+00:00
-- url     : https://prove2.me/theorems/f6e603ca-b036-43e1-882b-7acd4bf572f1
-- title:
--   Curvature Family Norm: nonempty weights
-- statement:
--   The Curvature Family Norm construction uses the nonempty weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/CurvatureFamilyNorm.lean#L181-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/CurvatureFamilyNorm.lean#L181-L276

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.nonempty_weights (X : Data E r) (h : Shape X) : Nonempty (Weights X) := by sorry
