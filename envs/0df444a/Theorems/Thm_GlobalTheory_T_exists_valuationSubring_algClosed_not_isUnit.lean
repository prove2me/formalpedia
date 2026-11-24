-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_valuationSubring_algClosed_not_isUnit
-- name    : GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:38:26.420952+00:00
-- url     : https://prove2.me/theorems/fce16f5b-c05a-4f2e-bd3e-905435173d27
-- title:
--   T: exists valuation Subring alg Closed not is Unit
-- statement:
--   The T construction uses the exists valuation Subring alg Closed not is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsValuationSubringAlgClosedNotIsUnitStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsValuationSubringAlgClosedNotIsUnitStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit : ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u → ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V), ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by sorry
