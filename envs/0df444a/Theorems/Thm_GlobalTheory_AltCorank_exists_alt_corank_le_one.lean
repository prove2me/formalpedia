-- Prove2me | Theorems.Thm_GlobalTheory_AltCorank_exists_alt_corank_le_one
-- name    : GlobalTheory.AltCorank.exists_alt_corank_le_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:57:02.697314+00:00
-- url     : https://prove2.me/theorems/2abcc368-5340-44bf-a51a-fbc6a04c38b7
-- title:
--   Alt Corank: exists alt corank le one
-- statement:
--   The Alt Corank construction uses the exists alt corank le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlternatingFormLeftCorankLeOne.lean#L108-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlternatingFormLeftCorankLeOne.lean#L108-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AltCorank
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.AltCorank.exists_alt_corank_le_one :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
      (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ →
      ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
        (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x := by sorry
