-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_muRoot_eq_one_iff
-- name    : GlobalTheory.PDivGroup.muRoot_eq_one_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:14.881873+00:00
-- url     : https://prove2.me/theorems/3af73795-161b-4e52-b9ed-2161acc4184c
-- title:
--   PDiv Group: mu Root eq one iff
-- statement:
--   The PDiv Group construction uses the mu Root eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L290-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L290-L294

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
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable {B : Type} [CommRing B] [Algebra O B]
variable [Fact p.Prime] {G}

theorem GlobalTheory.PDivGroup.muRoot_eq_one_iff (x : (mu p O).TateOver B) (n : ℕ) :
    muRoot x n = 1 ↔ ∃ y : (mu p O).TateOver B, (p : ℤ_[p]) ^ n • y = x := by sorry
