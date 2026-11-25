-- Prove2me | Theorems.Thm_GordanGenProof_mulOf_pos
-- name    : GordanGenProof.mulOf_pos
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:00.834752+00:00
-- url     : https://prove2.me/theorems/152e9d96-5f64-4855-80e5-8da1b7e5aad4
-- title:
--   Gordan Gen Proof: mul Of pos
-- statement:
--   The Gordan Gen Proof construction uses the mul Of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L361-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L361-L362

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

theorem GordanGenProof.mulOf_pos {n : ℕ} (v : Fin n → ℚ) : 0 < mulOf v := by sorry
