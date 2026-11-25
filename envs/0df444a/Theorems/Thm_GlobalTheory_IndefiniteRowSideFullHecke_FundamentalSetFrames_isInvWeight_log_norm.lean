-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FundamentalSetFrames_isInvWeight_log_norm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.isInvWeight_log_norm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:30.356411+00:00
-- url     : https://prove2.me/theorems/e1aabb0a-4ea2-520e-87ea-22d92a8cf010
-- title:
--   Fundamental Set Frames: is Inv Weight log norm
-- statement:
--   The Fundamental Set Frames construction uses the is Inv Weight log norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean#L45-L69

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.isInvWeight_log_norm (X : Data E r) (L : Wt X.Ψ r) (s : Frame X.Ψ r → ℂ)
    (hs : X.IsBddSec L s)
    (hinv : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.pnorm L s (lact γ (rmul x b)) = X.pnorm L s x) :
    IsInvWeight X fun x => ENNReal.log (ENNReal.ofReal (X.pnorm L s x ^ 2)) := by sorry
