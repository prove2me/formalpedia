-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_generators_of_card_hom_residueField_le
-- name    : GlobalTheory.T.exists_generators_of_card_hom_residueField_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:14.703972+00:00
-- url     : https://prove2.me/theorems/238573c3-4366-4e90-965c-c08b5c4b541b
-- title:
--   T: exists generators of card hom residue Field le
-- statement:
--   The T construction uses the exists generators of card hom residue Field le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGeneratorsOfCardHomResidueFieldLeStatement.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGeneratorsOfCardHomResidueFieldLeStatement.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGeneratorsOfCardHomResidueFieldLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGeneratorsOfCardHomResidueFieldLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_generators_of_card_hom_residueField_le : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)] (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ),
  Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ a →
  ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by sorry
