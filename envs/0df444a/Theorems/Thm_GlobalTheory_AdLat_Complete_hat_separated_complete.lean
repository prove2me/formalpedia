-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Complete_hat_separated_complete
-- name    : GlobalTheory.AdLat.Complete.hat_separated_complete
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:39:00.868774+00:00
-- url     : https://prove2.me/theorems/f42116db-e07a-4ec4-bde6-126b9a44a3dc
-- title:
--   Complete: hat separated complete
-- statement:
--   The Complete construction uses the hat separated complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionLatticeSeparatedComplete.lean#L262-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionLatticeSeparatedComplete.lean#L262-L287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Complete
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

theorem GlobalTheory.AdLat.Complete.hat_separated_complete : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ z : Fin n → _root_.GlobalTheory.AdLat.RA F E, (∀ N : ℕ, 0 < N →
      ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), z = N • w) → z = 0) ∧
    ∀ x : ℕ → (Fin n → _root_.GlobalTheory.AdLat.RA F E),
      (∀ N, x N ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)))) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        x (N * m) = x N + N • w) →
      ∃ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), ∀ N : ℕ, 0 < N →
        ∃ w ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), z = x N + N • w := by sorry
