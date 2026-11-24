-- Prove2me | Theorems.Thm_GlobalTheory_T_unitarySatakeCoeff_lastSignChange_of_leviReduction
-- name    : GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:50:17.523403+00:00
-- url     : https://prove2.me/theorems/68e0079d-fa9e-4f6e-a0e5-a7fddc68918e
-- title:
--   T: unitary Satake Coeff last Sign Change of levi Reduction
-- statement:
--   The T construction uses the unitary Satake Coeff last Sign Change of levi Reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffLastSignChangeOfLeviReductionStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffLastSignChangeOfLeviReductionStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReduction
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReductionStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction : GlobalTheory.SatakeWeyl.LeviStep → GlobalTheory.SatakeWeyl.IndexTwo → GlobalTheory.SatakeWeyl.IndexThree → GlobalTheory.SatakeWeyl.CoeffNeg := by sorry
