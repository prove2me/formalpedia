-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_padic_finiteDimensional_of_charZero
-- name    : GroundTheory.LocalField.exists_padic_finiteDimensional_of_charZero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:51.782795+00:00
-- url     : https://prove2.me/theorems/073cc870-605d-4904-b276-4f985ccce95e
-- title:
--   Local Field: exists padic finite Dimensional of char Zero
-- statement:
--   The Local Field construction uses the exists padic finite Dimensional of char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L191-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L191-L198

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel WithZero Topology

theorem GroundTheory.LocalField.exists_padic_finiteDimensional_of_charZero (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra ℚ_[p] K), p = ringChar 𝓀[K] ∧
      ValuativeExtension ℚ_[p] K ∧ FiniteDimensional ℚ_[p] K ∧
        Continuous (algebraMap ℚ_[p] K) := by sorry
