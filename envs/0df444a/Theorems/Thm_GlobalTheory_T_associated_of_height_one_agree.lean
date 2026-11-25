-- Prove2me | Theorems.Thm_GlobalTheory_T_associated_of_height_one_agree
-- name    : GlobalTheory.T.associated_of_height_one_agree
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:27.99242+00:00
-- url     : https://prove2.me/theorems/dc0548f8-35da-403d-b41d-be8236d1a378
-- title:
--   T: associated of height one agree
-- statement:
--   The T construction uses the associated of height one agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/AssociatedOfHeightOneAgree.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/AssociatedOfHeightOneAgree.lean#L5-L6

import Mathlib
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AssociatedOfHeightOneAgree
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AssociatedOfHeightOneAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem GlobalTheory.T.associated_of_height_one_agree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (a b : R), a ≠ 0 → b ≠ 0 → (∀ j ∈ J, IsUnit (π j) ∨ Prime (π j)) → (∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b) → (∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) → ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) → ∃ u : Rˣ, a = u * b := by sorry
