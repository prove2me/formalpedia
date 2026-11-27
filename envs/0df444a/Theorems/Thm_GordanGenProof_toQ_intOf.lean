-- Prove2me | Theorems.Thm_GordanGenProof_toQ_intOf
-- name    : GordanGenProof.toQ_intOf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:51:35.787799+00:00
-- url     : https://prove2.me/theorems/bd090e51-3bcb-5205-bf52-d4abf1e95ac7
-- title:
--   Gordan Gen Proof: to Q int Of
-- statement:
--   The Gordan Gen Proof construction uses the to Q int Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L364-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L364-L365

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

theorem GordanGenProof.toQ_intOf {n : ℕ} (v : Fin n → ℚ) : GordanCones.toQ (intOf v) = mulOf v • v := by sorry
