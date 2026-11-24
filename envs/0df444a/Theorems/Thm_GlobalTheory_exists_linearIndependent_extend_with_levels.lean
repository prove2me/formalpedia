-- Prove2me | Theorems.Thm_GlobalTheory_exists_linearIndependent_extend_with_levels
-- name    : GlobalTheory.exists_linearIndependent_extend_with_levels
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:15.957895+00:00
-- url     : https://prove2.me/theorems/9626a627-455a-4191-9daf-c6e4118d4071
-- title:
--   Global Theory: exists linear Independent extend with levels
-- statement:
--   The Global Theory construction uses the exists linear Independent extend with levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentAdaptedToDecreasingChainA.lean#L37-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentAdaptedToDecreasingChainA.lean#L37-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentAdaptedToDecreasingChainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.exists_linearIndependent_extend_with_levels {G : Type} [AddCommGroup G] (S : ℕ → Set G) {k : ℕ} (f : Fin k → G)
    (hf : LinearIndependent ℤ f) (hfS : ∀ j, f j ∈ S 0) (m : ℕ) (e : Fin m → G) (n : Fin m → ℕ)
    (he : LinearIndependent ℤ e) (heS : ∀ j, e j ∈ S (n j)) :
    ∀ k', m ≤ k' → k' ≤ k → ∃ (e2 : Fin k' → G) (n2 : Fin k' → ℕ), LinearIndependent ℤ e2 ∧
      (∀ j, e2 j ∈ S (n2 j)) ∧ ∑ j, n2 j = ∑ j, n j := by sorry
