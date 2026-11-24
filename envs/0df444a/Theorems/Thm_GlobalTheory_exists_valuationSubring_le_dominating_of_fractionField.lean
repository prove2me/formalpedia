-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_le_dominating_of_fractionField
-- name    : GlobalTheory.exists_valuationSubring_le_dominating_of_fractionField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:13.549393+00:00
-- url     : https://prove2.me/theorems/a630604f-0782-41fa-bd1e-d4037b4af31d
-- title:
--   Global Theory: exists valuation Subring le dominating of fraction Field
-- statement:
--   The Global Theory construction uses the exists valuation Subring le dominating of fraction Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean#L79-L86

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

theorem GlobalTheory.exists_valuationSubring_le_dominating_of_fractionField :
    ∀ (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
      [Algebra O F] [IsFractionRing O F] [Field L] (ι : F →+* L) (W : ValuationSubring L),
      (∀ x, ι x ∈ W) → ∃ W' : ValuationSubring L, W' ≤ W ∧
        (∀ x : O, ι (algebraMap O F x) ∈ W') ∧
        ∀ x ∈ IsLocalRing.maximalIdeal O, ι (algebraMap O F x) ∈ W'.nonunits := by sorry
