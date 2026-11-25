-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_TateOver_pow_smul_conv
-- name    : GlobalTheory.PDivGroup.TateOver.pow_smul_conv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:10:54.501879+00:00
-- url     : https://prove2.me/theorems/c8eee2ea-cf38-4981-95cb-53f58b931eb1
-- title:
--   Tate Over: pow smul conv
-- statement:
--   The Tate Over construction uses the pow smul conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L219-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L219-L222

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

theorem GlobalTheory.PDivGroup.TateOver.pow_smul_conv (x : G.TateOver B) (k n : ℕ) :
    ((p : ℤ_[p]) ^ k • x).conv n = x.conv n ^ p ^ k := by sorry
