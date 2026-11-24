-- Prove2me | Theorems.Thm_GlobalTheory_exists_span_eq_top_of_card_hom_residueField_le
-- name    : GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:04.928586+00:00
-- url     : https://prove2.me/theorems/b0de9d45-e8fc-434d-93c3-30e0d2a832a6
-- title:
--   Global Theory: exists span eq top of card hom residue Field le
-- statement:
--   The Global Theory construction uses the exists span eq top of card hom residue Field le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGeneratorsOfCardHomResidueFieldLe.lean#L7-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGeneratorsOfCardHomResidueFieldLe.lean#L7-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGeneratorsOfCardHomResidueFieldLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le
    (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ)
    (h : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤
      Nat.card (IsLocalRing.ResidueField Λ) ^ a) :
    ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by sorry
