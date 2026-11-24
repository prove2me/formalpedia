-- Prove2me | Theorems.Thm_GlobalTheory_SaturatedNotDvd_main
-- name    : GlobalTheory.SaturatedNotDvd.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:48:39.061326+00:00
-- url     : https://prove2.me/theorems/e906754c-2178-4ceb-a325-5bd442b68843
-- title:
--   Saturated Not Dvd: main
-- statement:
--   The Saturated Not Dvd construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSaturated.lean#L58-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSaturated.lean#L58-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.SaturatedNotDvd

theorem GlobalTheory.SaturatedNotDvd.main : (let d1 : (A : Type u_1) → [CommRing A] → Prop := @(fun (A : Type u_1) [CommRing A] ↦ ∀ (a b : A) (I : Ideal A), b ≠ (0 : A) → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a); ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}, Prime x → d1 (A ⧸ Ideal.span {x}) → ∀ {a b : A}, ¬x ∣ b → ∀ {I : Ideal A}, I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a) := by sorry
