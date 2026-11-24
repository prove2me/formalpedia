-- Prove2me | Theorems.Thm_GordanGenProof_fm_scalar
-- name    : GordanGenProof.fm_scalar
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:50.720957+00:00
-- url     : https://prove2.me/theorems/9e3aa675-3a43-4ed6-872f-fa30150d6333
-- title:
--   Gordan Gen Proof: fm scalar
-- statement:
--   The Gordan Gen Proof construction uses the fm scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L60-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L60-L116

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset

theorem GordanGenProof.fm_scalar {κ : Type*} (P : Finset κ) (u c : κ → ℚ) :
    (∃ t : ℚ, ∀ p ∈ P, 0 ≤ u p + c p * t) ↔
      (∀ p ∈ P, c p = 0 → 0 ≤ u p) ∧
      (∀ p ∈ P, ∀ q ∈ P, 0 < c p → c q < 0 → 0 ≤ c p * u q - c q * u p) := by sorry
