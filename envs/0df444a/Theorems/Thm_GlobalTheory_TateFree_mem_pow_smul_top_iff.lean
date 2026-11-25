-- Prove2me | Theorems.Thm_GlobalTheory_TateFree_mem_pow_smul_top_iff
-- name    : GlobalTheory.TateFree.mem_pow_smul_top_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:08.416881+00:00
-- url     : https://prove2.me/theorems/48aa8a14-4605-4afc-b775-e3da13e253d8
-- title:
--   Tate Free: mem pow smul top iff
-- statement:
--   The Tate Free construction uses the mem pow smul top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L75-L80

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

theorem GlobalTheory.TateFree.mem_pow_smul_top_iff (n : ℕ) (x : M) :
    x ∈ (IsLocalRing.maximalIdeal ℤ_[p] ^ n • ⊤ : Submodule ℤ_[p] M) ↔
      ∃ y, (p : ℤ_[p]) ^ n • y = x := by sorry
