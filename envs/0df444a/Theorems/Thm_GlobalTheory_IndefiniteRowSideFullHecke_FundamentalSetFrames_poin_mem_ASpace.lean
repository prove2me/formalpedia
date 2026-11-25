-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FundamentalSetFrames_poin_mem_ASpace
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.poin_mem_ASpace
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:44.665376+00:00
-- url     : https://prove2.me/theorems/3f0ebcba-19f2-404b-ac09-38ba010c95ee
-- title:
--   Fundamental Set Frames: poin mem ASpace
-- statement:
--   The Fundamental Set Frames construction uses the poin mem ASpace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean#L166-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean#L166-L174

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.poin_mem_ASpace (h : PoincareCuspidalStatement E) (X : Data E r) (x0 : Frame X.Ψ r)
    (hx0 : IsOrth X x0) (bb : ℝ) (hb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb) (la : Wt X.Ψ r)
    (hg : GapsNonneg X la)
    (hp : ∀ (h0 : 0 < X.p0) (h1 : X.p0 < r), ∃ τ : X.Ψ, 0 < pairing X h0 h1 la τ)
    (u : Frame X.Ψ r → EReal) (hu : IsInvWeight X u) (F : V (nd X) → ℂ)
    (hF : F ∈ ATilde X x0 bb la u) (P : Frame X.Ψ r → ℂ) (hP : IsExt X x0 la F P)
    (FF : Set (V (nd X))) (hFF : IsFundSet X x0 FF) : poin X la P ∈ ASpace X x0 la u FF := by sorry
