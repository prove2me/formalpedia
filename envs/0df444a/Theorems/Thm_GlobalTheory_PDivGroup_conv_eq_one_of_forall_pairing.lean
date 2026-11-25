-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_conv_eq_one_of_forall_pairing
-- name    : GlobalTheory.PDivGroup.conv_eq_one_of_forall_pairing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:55:09.916801+00:00
-- url     : https://prove2.me/theorems/c4c61aec-bc11-4e68-9a91-66b0ac5512a2
-- title:
--   PDiv Group: conv eq one of forall pairing
-- statement:
--   The PDiv Group construction uses the conv eq one of forall pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L386-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L386-L392

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
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]

theorem GlobalTheory.PDivGroup.conv_eq_one_of_forall_pairing (χ : G.dual.Tate) (n : ℕ)
    (h : ∀ t : G.Tate, muRoot (pairing G O t χ) n = 1) : χ.conv n = 1 := by sorry
