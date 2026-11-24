-- Prove2me | Theorems.Thm_GordanGenProof_mem_gcone_insert
-- name    : GordanGenProof.mem_gcone_insert
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:20.829607+00:00
-- url     : https://prove2.me/theorems/31bbb5c8-36d9-4545-986d-a295f9cb392e
-- title:
--   Gordan Gen Proof: mem gcone insert
-- statement:
--   The Gordan Gen Proof construction uses the mem gcone insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L35-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L35-L58

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

theorem GordanGenProof.mem_gcone_insert {n : ℕ} {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → Fin n → ℚ}
    {w : ι} (hw : w ∉ s) (x : Fin n → ℚ) :
    x ∈ gcone (insert w s) f ↔ ∃ t : ℚ, 0 ≤ t ∧ x - t • f w ∈ gcone s f := by sorry
