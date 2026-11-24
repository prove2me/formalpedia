-- Prove2me | Theorems.Thm_GordanGenProof_fm_dot
-- name    : GordanGenProof.fm_dot
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:43.656471+00:00
-- url     : https://prove2.me/theorems/46c915be-7312-4c96-b5c8-dfd77ee7d37d
-- title:
--   Gordan Gen Proof: fm dot
-- statement:
--   The Gordan Gen Proof construction uses the fm dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L123-L129

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

theorem GordanGenProof.fm_dot {n : ℕ} (a b : ℚ) (u v x : Fin n → ℚ) :
    (a • u - b • v) ⬝ᵥ x = a * (u ⬝ᵥ x) - b * (v ⬝ᵥ x) := by sorry
