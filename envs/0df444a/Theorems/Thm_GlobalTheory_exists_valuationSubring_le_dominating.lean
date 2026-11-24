-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_le_dominating
-- name    : GlobalTheory.exists_valuationSubring_le_dominating
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:44.293823+00:00
-- url     : https://prove2.me/theorems/76f556af-540b-4d8d-8bc9-bda7031346a3
-- title:
--   Global Theory: exists valuation Subring le dominating
-- statement:
--   The Global Theory construction uses the exists valuation Subring le dominating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean#L56-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean#L56-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
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

theorem GlobalTheory.exists_valuationSubring_le_dominating {O L : Type*} [CommRing O] [IsLocalRing O]
    [Field L] (g : O →+* L) (W : ValuationSubring L) (hg : ∀ x, g x ∈ W) :
    ∃ W' : ValuationSubring L, W' ≤ W ∧ (∀ x : O, g x ∈ W') ∧
      ∀ x ∈ maximalIdeal O, g x ∈ W'.nonunits := by sorry
