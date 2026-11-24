-- Prove2me | Theorems.Thm_GlobalTheory_exists_generator_sq_eq_of_sq_mem_zpowers
-- name    : GlobalTheory.exists_generator_sq_eq_of_sq_mem_zpowers
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:17.972919+00:00
-- url     : https://prove2.me/theorems/e0846fcf-2b16-487f-8881-d2adcd2a5c60
-- title:
--   Global Theory: exists generator sq eq of sq mem zpowers
-- statement:
--   The Global Theory construction uses the exists generator sq eq of sq mem zpowers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsGeneratorSqEqOfSqMemZpowers.lean#L5-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsGeneratorSqEqOfSqMemZpowers.lean#L5-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsGeneratorSqEqOfSqMemZpowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_generator_sq_eq_of_sq_mem_zpowers :
    ∀ (p : ℕ), p.Prime → ∀ a : (ZMod p)ˣ,
      (∀ b : (ZMod p)ˣ, b ^ 2 ∈ Subgroup.zpowers (a ^ 2)) →
      ∃ γ : (ZMod p)ˣ, Subgroup.zpowers γ = ⊤ ∧ γ ^ 2 = a ^ 2 := by sorry
