-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FundamentalSetFrames_zero_mem_ATilde
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.zero_mem_ATilde
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:56.687856+00:00
-- url     : https://prove2.me/theorems/489c4bde-6099-4773-9838-8d974497a567
-- title:
--   Fundamental Set Frames: zero mem ATilde
-- statement:
--   The Fundamental Set Frames construction uses the zero mem ATilde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FundamentalSetFrames.lean#L90-L92

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.zero_mem_ATilde (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r)
    (u : Frame X.Ψ r → EReal) : (fun _ => 0) ∈ ATilde X x0 bb la u := by sorry
