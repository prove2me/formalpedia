-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_TateOver_eq_zero_of_forall_pow_smul
-- name    : GlobalTheory.PDivGroup.TateOver.eq_zero_of_forall_pow_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:53:07.294197+00:00
-- url     : https://prove2.me/theorems/06d718e3-93aa-4523-9168-bd3061a33507
-- title:
--   Tate Over: eq zero of forall pow smul
-- statement:
--   The Tate Over construction uses the eq zero of forall pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L257-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L257-L259

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

theorem GlobalTheory.PDivGroup.TateOver.eq_zero_of_forall_pow_smul (t : G.TateOver B)
    (h : ∀ n, ∃ s : G.TateOver B, (p : ℤ_[p]) ^ n • s = t) : t = 0 := by sorry
