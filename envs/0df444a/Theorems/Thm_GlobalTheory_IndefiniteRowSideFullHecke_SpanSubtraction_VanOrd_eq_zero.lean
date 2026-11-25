-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SpanSubtraction_VanOrd_eq_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.VanOrd.eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:49.037858+00:00
-- url     : https://prove2.me/theorems/b01c1673-4a3e-4e9c-9be7-4dd576b71fc9
-- title:
--   Van Ord: eq zero
-- statement:
--   The Van Ord construction uses the eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/SpanSubtraction.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/SpanSubtraction.lean#L92-L101

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.VanOrd.eq_zero {X : Data E r} {Xa : ArchInM X} {Fl : FlatM X Xa} {a : ℕ} (ha : a ≠ 0)
    {f : Frame X.Ψ r → ℂ} (hf : VanOrd Fl a f) (j : Fin Fl.δ)
    (hs : ∀ k, Fl.s k (cpt X (Fl.xs j) 0) = 0) : f (cpt X (Fl.xs j) 0) = 0 := by sorry
