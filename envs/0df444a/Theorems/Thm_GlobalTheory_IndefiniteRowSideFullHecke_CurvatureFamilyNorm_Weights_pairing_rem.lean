-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CurvatureFamilyNorm_Weights_pairing_rem
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.pairing_rem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:04.918358+00:00
-- url     : https://prove2.me/theorems/8884b10f-1b5e-462b-8958-c6a75ba10a78
-- title:
--   Weights: pairing rem
-- statement:
--   The Weights construction uses the pairing rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/CurvatureFamilyNorm.lean#L112-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/CurvatureFamilyNorm.lean#L112-L123

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.Weights.pairing_rem (τ : X.Ψ) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) + 1 = r) :
    2 * (w.hF : ℤ) + 2 ≤ w.rem τ b - w.rem τ a := by sorry
