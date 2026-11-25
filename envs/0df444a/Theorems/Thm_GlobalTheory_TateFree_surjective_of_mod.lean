-- Prove2me | Theorems.Thm_GlobalTheory_TateFree_surjective_of_mod
-- name    : GlobalTheory.TateFree.surjective_of_mod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:01.595786+00:00
-- url     : https://prove2.me/theorems/a812568c-d10d-43a0-965c-3080e12549d4
-- title:
--   Tate Free: surjective of mod
-- statement:
--   The Tate Free construction uses the surjective of mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L82-L93

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

theorem GlobalTheory.TateFree.surjective_of_mod (f : M →ₗ[ℤ_[p]] N) [Module.Finite ℤ_[p] M]
    (hN : ∀ y : N, (∀ n, ∃ z, (p : ℤ_[p]) ^ n • z = y) → y = 0)
    (h : ∀ y, ∃ x z, (p : ℤ_[p]) • z = y - f x) : Function.Surjective f := by sorry
