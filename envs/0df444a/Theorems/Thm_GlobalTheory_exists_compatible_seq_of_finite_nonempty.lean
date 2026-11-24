-- Prove2me | Theorems.Thm_GlobalTheory_exists_compatible_seq_of_finite_nonempty
-- name    : GlobalTheory.exists_compatible_seq_of_finite_nonempty
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:31.520515+00:00
-- url     : https://prove2.me/theorems/47fbe5c7-3431-4127-8ef5-9e744f3da969
-- title:
--   Global Theory: exists compatible seq of finite nonempty
-- statement:
--   The Global Theory construction uses the exists compatible seq of finite nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompatibleSeqOfFiniteNonempty.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompatibleSeqOfFiniteNonempty.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleSeqOfFiniteNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open GlobalTheory

theorem GlobalTheory.exists_compatible_seq_of_finite_nonempty
    (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n))
    (hfin : ∀ n, (Y n).Finite) (hne : ∀ n, (Y n).Nonempty)
    (hmap : ∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) :
    ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by sorry
