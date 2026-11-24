-- Prove2me | Theorems.Thm_GlobalTheory_torsionBy_two_generators_mod_prime
-- name    : GlobalTheory.torsionBy_two_generators_mod_prime
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:29.451074+00:00
-- url     : https://prove2.me/theorems/df61eb65-0726-49b8-a9d6-9162ce9a0eb0
-- title:
--   Global Theory: torsion By two generators mod prime
-- statement:
--   The Global Theory construction uses the torsion By two generators mod prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionTwoGeneratorsModPrime.lean#L8-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionTwoGeneratorsModPrime.lean#L8-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsModPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open scoped Pointwise

theorem GlobalTheory.torsionBy_two_generators_mod_prime :
  ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 →
    ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
      x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) := by sorry
