-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedHensel_subset_of_unramified
-- name    : GlobalTheory.UnramifiedHensel.subset_of_unramified
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:36.475019+00:00
-- url     : https://prove2.me/theorems/1ab5000a-65fc-5b63-9724-fa50d70f27c8
-- title:
--   Unramified Hensel: subset of unramified
-- statement:
--   The Unramified Hensel construction uses the subset of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L205-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L205-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel

theorem GlobalTheory.UnramifiedHensel.subset_of_unramified (K : Type) [NormedField K] [IsUltrametricDist K] (W : Subring K)
    (hW : IsClosed (W : Set K)) (hc : ∀ w ∈ W, ‖w‖ ≤ 1)
    (hres : ∀ x : K, ‖x‖ ≤ 1 → ∃ w ∈ W, ‖x - w‖ < 1) (s : Set K) (hs : s.Finite)
    (hs1 : ∀ x ∈ s, ‖x‖ ≤ 1)
    (h : ∀ (k : Type) [Field k] (φ : Subring.closure ((W : Set K) ∪ s) →+* DualNumber k),
      (∀ a : Subring.closure ((W : Set K) ∪ s), ‖(a : K)‖ = 1 → (φ a).fst ≠ 0) →
      (∀ a : Subring.closure ((W : Set K) ∪ s), (a : K) ∈ W → (φ a).snd = 0) →
      ∀ a : Subring.closure ((W : Set K) ∪ s), (a : K) ∈ s → (φ a).snd = 0) :
    s ⊆ (W : Set K) := by sorry
