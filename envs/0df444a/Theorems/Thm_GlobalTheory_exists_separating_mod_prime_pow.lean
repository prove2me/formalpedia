-- Prove2me | Theorems.Thm_GlobalTheory_exists_separating_mod_prime_pow
-- name    : GlobalTheory.exists_separating_mod_prime_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:49.778239+00:00
-- url     : https://prove2.me/theorems/6c4c00f3-fde1-4dfc-b32e-886186d1eb23
-- title:
--   Global Theory: exists separating mod prime pow
-- statement:
--   The Global Theory construction uses the exists separating mod prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsSeparatingModPrimePow.lean#L14-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsSeparatingModPrimePow.lean#L14-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HomValueCongruentIntModPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsUnitSubOfRingHomNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsSeparatingModPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_separating_mod_prime_pow : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (T : Type) [Fintype T] [DecidableEq T] (σ : T → A →+* O), Function.Injective σ → ∀ (K : ℕ) (t₀ : T), ∃ e : A, ∀ t, σ t e - (if t = t₀ then 1 else 0) ∈ Ideal.span {(g : O) ^ K} := by sorry
