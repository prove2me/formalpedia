-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_norm_iff
-- name    : GlobalTheory.CuspCharCheck.norm_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:15.019859+00:00
-- url     : https://prove2.me/theorems/a1283dda-c82d-4221-bfc8-49bae4cabd25
-- title:
--   Cusp Char Check: norm iff
-- statement:
--   The Cusp Char Check construction uses the norm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L26-L29

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {G : Type} [Group G]

theorem GlobalTheory.CuspCharCheck.norm_iff [Fintype G] (V : FDRep ℂ G) :
    (∑ x, V.character x * star (V.character x)) = (Fintype.card G : ℂ) ↔ Simple V := by sorry
