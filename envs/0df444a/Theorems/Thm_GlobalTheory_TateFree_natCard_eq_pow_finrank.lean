-- Prove2me | Theorems.Thm_GlobalTheory_TateFree_natCard_eq_pow_finrank
-- name    : GlobalTheory.TateFree.natCard_eq_pow_finrank
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:53:50.271999+00:00
-- url     : https://prove2.me/theorems/9877a608-0b64-45cf-b236-e918ebb8db02
-- title:
--   Tate Free: nat Card eq pow finrank
-- statement:
--   The Tate Free construction uses the nat Card eq pow finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L95-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L95-L125

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
variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup N]
  [Module ℤ_[p] N]

theorem GlobalTheory.TateFree.natCard_eq_pow_finrank [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M] {X : Type}
    [AddCommGroup X] (f : M →+ X) (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 ↔ ∃ y, (p : ℤ_[p]) • y = x) : Nat.card X = p ^ finrank ℤ_[p] M := by sorry
