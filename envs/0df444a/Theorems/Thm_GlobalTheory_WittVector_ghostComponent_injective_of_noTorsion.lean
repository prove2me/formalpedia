-- Prove2me | Theorems.Thm_GlobalTheory_WittVector_ghostComponent_injective_of_noTorsion
-- name    : GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:18.235075+00:00
-- url     : https://prove2.me/theorems/1f3ad74e-47a9-4967-a67e-2a75694606c5
-- title:
--   Witt Vector: ghost Component injective of no Torsion
-- statement:
--   The Witt Vector construction uses the ghost Component injective of no Torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GhostComponentInjectiveOfNoTorsion.lean#L6-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GhostComponentInjectiveOfNoTorsion.lean#L6-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GhostComponentInjectiveOfNoTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory

theorem GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
      ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by sorry
