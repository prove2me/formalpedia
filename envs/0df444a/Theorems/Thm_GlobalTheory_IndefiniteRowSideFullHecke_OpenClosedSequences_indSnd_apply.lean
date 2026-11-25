-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_indSnd_apply
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.indSnd_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:59.28382+00:00
-- url     : https://prove2.me/theorems/239cdaee-de7f-4ad2-9eb7-8ad641ab94ff
-- title:
--   Open Closed Sequences: ind Snd apply
-- statement:
--   The Open Closed Sequences construction uses the ind Snd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/OpenClosedSequences.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/OpenClosedSequences.lean#L56-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n Γ W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Group Γ] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.indSnd_apply (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (γ : Γ)
    (h x : GL n k) (f) : (indSnd e τ (γ, h) f).1.1 x = τ (γ, 1) (f.1.1 (x * h)) := by sorry
