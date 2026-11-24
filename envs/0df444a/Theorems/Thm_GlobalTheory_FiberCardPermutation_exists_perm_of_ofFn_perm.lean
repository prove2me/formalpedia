-- Prove2me | Theorems.Thm_GlobalTheory_FiberCardPermutation_exists_perm_of_ofFn_perm
-- name    : GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:58.466525+00:00
-- url     : https://prove2.me/theorems/52f27777-84d4-47b5-acdd-464423ac57aa
-- title:
--   Fiber Card Permutation: exists perm of of Fn perm
-- statement:
--   The Fiber Card Permutation construction uses the exists perm of of Fn perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPermOfOfFnPerm.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPermOfOfFnPerm.lean#L12-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FiberCardPermutation

theorem GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : List.Perm (List.ofFn v) (List.ofFn w)) :
    ∃ σ : Equiv.Perm (Fin n), v = w ∘ (⇑σ : Fin n → Fin n) := by sorry
