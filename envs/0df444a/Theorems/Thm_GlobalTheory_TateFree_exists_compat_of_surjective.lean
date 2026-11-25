-- Prove2me | Theorems.Thm_GlobalTheory_TateFree_exists_compat_of_surjective
-- name    : GlobalTheory.TateFree.exists_compat_of_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:11.527604+00:00
-- url     : https://prove2.me/theorems/0f8909c3-cf85-47ce-902c-af0b9498ef34
-- title:
--   Tate Free: exists compat of surjective
-- statement:
--   The Tate Free construction uses the exists compat of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L14-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.TateFree

theorem GlobalTheory.TateFree.exists_compat_of_surjective (n : ℕ) : ∀ (X : ℕ → Type) (π : ∀ k, X (k + 1) → X k),
    (∀ k, Function.Surjective (π k)) → ∀ x : X n,
      ∃ s : ∀ k, X k, (∀ k, π k (s (k + 1)) = s k) ∧ s n = x := by sorry
