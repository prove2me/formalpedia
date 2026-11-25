-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_TateOver_conv_eq_one_iff
-- name    : GlobalTheory.PDivGroup.TateOver.conv_eq_one_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:01.378908+00:00
-- url     : https://prove2.me/theorems/b07464e8-b0c5-4246-b1e3-34f69db1756c
-- title:
--   Tate Over: conv eq one iff
-- statement:
--   The Tate Over construction uses the conv eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L244-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L244-L255

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

theorem GlobalTheory.PDivGroup.TateOver.conv_eq_one_iff (t : G.TateOver B) (n : ℕ) :
    t.conv n = 1 ↔ ∃ s : G.TateOver B, (p : ℤ_[p]) ^ n • s = t := by sorry
