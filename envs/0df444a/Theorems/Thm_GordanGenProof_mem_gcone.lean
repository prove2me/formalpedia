-- Prove2me | Theorems.Thm_GordanGenProof_mem_gcone
-- name    : GordanGenProof.mem_gcone
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:28.119856+00:00
-- url     : https://prove2.me/theorems/b5895074-4ced-484c-a8e4-4fc583b19e07
-- title:
--   Gordan Gen Proof: mem gcone
-- statement:
--   The Gordan Gen Proof construction uses the mem gcone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L28-L33

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

theorem GordanGenProof.mem_gcone {n : ℕ} {ι : Type*} {s : Finset ι} {f : ι → Fin n → ℚ} {i : ι} (hi : i ∈ s) :
    f i ∈ gcone s f := by sorry
