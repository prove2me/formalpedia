-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FundamentalSetFrames_pairing_kapW
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.pairing_kapW
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:35.454912+00:00
-- url     : https://prove2.me/theorems/6f9b42b5-8ebc-5e3b-84ab-3c84ce3eb033
-- title:
--   Fundamental Set Frames: pairing kap W
-- statement:
--   The Fundamental Set Frames construction uses the pairing kap W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean#L23-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FundamentalSetFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ENNReal NNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.pairing_kapW (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) (τ : X.Ψ) :
    pairing X h0 h1 (kapW X) τ = 2 * (r : ℤ) - 2 := by sorry
