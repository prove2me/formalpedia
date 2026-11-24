-- Prove2me | Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_of_subring
-- name    : GlobalTheory.exists_discreteValuationSubring_of_subring
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:19.13837+00:00
-- url     : https://prove2.me/theorems/9d812bf9-3dd0-42a1-b30f-a2c205f8cd1b
-- title:
--   Global Theory: exists discrete Valuation Subring of subring
-- statement:
--   The Global Theory construction uses the exists discrete Valuation Subring of subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L168-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L168-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {L : Type*} [Field L]

theorem GlobalTheory.exists_discreteValuationSubring_of_subring (B : Subring L) [IsNoetherianRing B]
    (hB : ∀ z : L, ∃ c ∈ B, c ≠ 0 ∧ c * z ∈ B) {y : L} (hy : y ∈ B) (hy0 : y ≠ 0)
    (hy1 : y⁻¹ ∉ B) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ B ≤ V.toSubring ∧ y ∈ V.nonunits := by sorry
