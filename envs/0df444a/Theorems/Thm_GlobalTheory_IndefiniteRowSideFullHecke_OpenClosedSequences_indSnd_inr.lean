-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_indSnd_inr
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.indSnd_inr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:23.238906+00:00
-- url     : https://prove2.me/theorems/c5e76df7-1e5a-483b-adc1-34d0cf636008
-- title:
--   Open Closed Sequences: ind Snd inr
-- statement:
--   The Open Closed Sequences construction uses the ind Snd inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/OpenClosedSequences.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/OpenClosedSequences.lean#L59-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.indSnd_inr (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (h : GL n k) :
    indSnd e τ (1, h) = ind₂ e (τ.comp (MonoidHom.inr Γ _)) h := by sorry
