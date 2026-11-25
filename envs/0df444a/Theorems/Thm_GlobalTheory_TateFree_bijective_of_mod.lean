-- Prove2me | Theorems.Thm_GlobalTheory_TateFree_bijective_of_mod
-- name    : GlobalTheory.TateFree.bijective_of_mod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:09.937491+00:00
-- url     : https://prove2.me/theorems/438e6194-9849-4fd7-adf0-0dcf7fdf472d
-- title:
--   Tate Free: bijective of mod
-- statement:
--   The Tate Free construction uses the bijective of mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L127-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L127-L162

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

theorem GlobalTheory.TateFree.bijective_of_mod [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] N]
    [Module.Free ℤ_[p] N] (f : M →ₗ[ℤ_[p]] N) (hr : finrank ℤ_[p] M = finrank ℤ_[p] N)
    (h : ∀ x, (∃ z, (p : ℤ_[p]) • z = f x) → ∃ y, (p : ℤ_[p]) • y = x) :
    Function.Bijective f := by sorry
