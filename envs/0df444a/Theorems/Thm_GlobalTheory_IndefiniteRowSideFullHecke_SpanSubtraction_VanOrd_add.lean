-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SpanSubtraction_VanOrd_add
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.VanOrd.add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:53.55282+00:00
-- url     : https://prove2.me/theorems/c0d4a979-5492-4530-868d-f041e5a391e5
-- title:
--   Van Ord: add
-- statement:
--   The Van Ord construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/SpanSubtraction.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/SpanSubtraction.lean#L88-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_SpanSubtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology Asymptotics
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.VanOrd.add {X : Data E r} {Xa : ArchInM X} {Fl : FlatM X Xa} {a : ℕ}
    {f g : Frame X.Ψ r → ℂ} (hf : VanOrd Fl a f) (hg : VanOrd Fl a g) :
    VanOrd Fl a fun x => f x + g x := by sorry
