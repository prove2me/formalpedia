-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ExhaustionFrames_zDet_pos
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames.zDet_pos
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:44:50.604139+00:00
-- url     : https://prove2.me/theorems/7dd527ee-5175-4fdd-a04d-64bfbac46487
-- title:
--   Exhaustion Frames: z Det pos
-- statement:
--   The Exhaustion Frames construction uses the z Det pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/ExhaustionFrames.lean#L99-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/ExhaustionFrames.lean#L99-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames.zDet_pos {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) : 0 < zDet X z τ := by sorry
