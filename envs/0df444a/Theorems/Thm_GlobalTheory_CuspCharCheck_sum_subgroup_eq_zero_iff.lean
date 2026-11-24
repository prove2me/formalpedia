-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_sum_subgroup_eq_zero_iff
-- name    : GlobalTheory.CuspCharCheck.sum_subgroup_eq_zero_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:26.932929+00:00
-- url     : https://prove2.me/theorems/8eb2c513-4733-4497-8bc9-10ddab442c63
-- title:
--   Cusp Char Check: sum subgroup eq zero iff
-- statement:
--   The Cusp Char Check construction uses the sum subgroup eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L40-L56

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

theorem GlobalTheory.CuspCharCheck.sum_subgroup_eq_zero_iff [Fintype G] (V : FDRep ℂ G) (U : Subgroup G) [DecidablePred (· ∈ U)] :
    (∑ u : G, if u ∈ U then V.character u else 0) = 0 ↔ ∀ v : V, (∀ u ∈ U, V.ρ u v = v) → v = 0 := by sorry
