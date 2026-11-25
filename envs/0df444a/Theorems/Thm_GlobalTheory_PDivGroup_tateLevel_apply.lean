-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_tateLevel_apply
-- name    : GlobalTheory.PDivGroup.tateLevel_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:44.578656+00:00
-- url     : https://prove2.me/theorems/db612c2b-4e9d-40bf-9eb5-07ed8b697ef1
-- title:
--   PDiv Group: tate Level apply
-- statement:
--   The PDiv Group construction uses the tate Level apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L287-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L287-L288

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

theorem GlobalTheory.PDivGroup.tateLevel_apply (n : ℕ) (t : G.Tate) :
    tateLevel G n t = Additive.ofMul (t.conv n) := by sorry

attribute [defeq] GlobalTheory.PDivGroup.tateLevel_apply
