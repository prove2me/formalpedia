-- Prove2me | Theorems.Thm_GlobalTheory_ProjModClasses_exists_equiv_model
-- name    : GlobalTheory.ProjModClasses.exists_equiv_model
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:16.073133+00:00
-- url     : https://prove2.me/theorems/7951525f-91cb-4eee-9cca-489457c716e7
-- title:
--   Proj Mod Classes: exists equiv model
-- statement:
--   The Proj Mod Classes construction uses the exists equiv model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFinRepsProjectiveFinrankLeNumberField.lean#L50-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFinRepsProjectiveFinrankLeNumberField.lean#L50-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField
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
open GlobalTheory.ProjModClasses
variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]

theorem GlobalTheory.ProjModClasses.exists_equiv_model : ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.Projective R X], Module.finrank R X = r →
    ∃ c : Fin r → ClassGroup R, Nonempty (X ≃ₗ[R] Model c)
  := by sorry
