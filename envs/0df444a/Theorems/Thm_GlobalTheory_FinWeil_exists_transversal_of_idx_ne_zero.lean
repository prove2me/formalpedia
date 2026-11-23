-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_exists_transversal_of_idx_ne_zero
-- name    : GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:39.159947+00:00
-- url     : https://prove2.me/theorems/6d851735-5d9e-4e87-8106-0710991fe2fc
-- title:
--   Fin Weil: exists transversal of idx ne zero
-- statement:
--   The Fin Weil construction uses the exists transversal of idx ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversal.lean#L89-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversal.lean#L89-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
open Classical
open scoped BigOperators
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero (A B : Submodule R X)
    (hi : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A := by sorry
