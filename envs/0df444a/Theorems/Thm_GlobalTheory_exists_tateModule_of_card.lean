-- Prove2me | Theorems.Thm_GlobalTheory_exists_tateModule_of_card
-- name    : GlobalTheory.exists_tateModule_of_card
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:45.417892+00:00
-- url     : https://prove2.me/theorems/4ae10d37-b248-4cdf-95de-e277cf0b5436
-- title:
--   Global Theory: exists tate Module of card
-- statement:
--   The Global Theory construction uses the exists tate Module of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean#L180-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean#L180-L285

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TateSeq

theorem GlobalTheory.exists_tateModule_of_card :
    ∀ (M : Type) [AddCommGroup M] (l r : ℕ) [Fact l.Prime], (∀ n, Nat.card {x : M // l ^ n • x = 0} = l ^ (r * n)) → ∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℤ_[l] T) (π : ℕ → T →+ M), Module.Free ℤ_[l] T ∧ Module.Finite ℤ_[l] T ∧ Module.finrank ℤ_[l] T = r ∧ (∀ n x, l • π (n + 1) x = π n x) ∧ (∀ x, π 0 x = 0) ∧ (∀ n (a : ℤ_[l]) x, π n (a • x) = (PadicInt.toZModPow n a).val • π n x) ∧ (∀ n y, l ^ n • y = 0 → ∃ x, π n x = y) ∧ (∀ n x, π n x = 0 ↔ ∃ y, x = l ^ n • y) ∧ ∀ s : ℕ → M, s 0 = 0 → (∀ n, l • s (n + 1) = s n) → ∃! x, ∀ n, π n x = s n := by sorry
