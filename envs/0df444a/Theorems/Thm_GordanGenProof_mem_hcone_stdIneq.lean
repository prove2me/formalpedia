-- Prove2me | Theorems.Thm_GordanGenProof_mem_hcone_stdIneq
-- name    : GordanGenProof.mem_hcone_stdIneq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:47.911654+00:00
-- url     : https://prove2.me/theorems/1eb7319d-9d3f-487a-b763-76494a09a2a2
-- title:
--   Gordan Gen Proof: mem hcone std Ineq
-- statement:
--   The Gordan Gen Proof construction uses the mem hcone std Ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L164-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L164-L187

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

theorem GordanGenProof.mem_hcone_stdIneq (n : ℕ) (x : Fin n → ℚ) : x ∈ hcone (stdIneq n) id ↔ x = 0 := by sorry
