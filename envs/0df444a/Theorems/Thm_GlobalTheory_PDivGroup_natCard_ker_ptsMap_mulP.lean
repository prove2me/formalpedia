-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_natCard_ker_ptsMap_mulP
-- name    : GlobalTheory.PDivGroup.natCard_ker_ptsMap_mulP
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:55:11.164423+00:00
-- url     : https://prove2.me/theorems/366616e4-205f-450b-8fc5-b60a3fd89c88
-- title:
--   PDiv Group: nat Card ker pts Map mul P
-- statement:
--   The PDiv Group construction uses the nat Card ker pts Map mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L193-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L193-L211

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

theorem GlobalTheory.PDivGroup.natCard_ker_ptsMap_mulP (n : ℕ) :
    Nat.card (pointsMap O (G.mulP n)).ker = Nat.card (G.A 1 →ₐ[O] O) := by sorry
