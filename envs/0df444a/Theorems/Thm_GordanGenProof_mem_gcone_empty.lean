-- Prove2me | Theorems.Thm_GordanGenProof_mem_gcone_empty
-- name    : GordanGenProof.mem_gcone_empty
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:30.63354+00:00
-- url     : https://prove2.me/theorems/9f27f6c1-1dad-4f1b-9219-8694d0aca398
-- title:
--   Gordan Gen Proof: mem gcone empty
-- statement:
--   The Gordan Gen Proof construction uses the mem gcone empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L189-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L189-L195

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

theorem GordanGenProof.mem_gcone_empty {n : ℕ} (x : Fin n → ℚ) :
    x ∈ gcone (∅ : Finset (Fin n → ℚ)) id ↔ x = 0 := by sorry
