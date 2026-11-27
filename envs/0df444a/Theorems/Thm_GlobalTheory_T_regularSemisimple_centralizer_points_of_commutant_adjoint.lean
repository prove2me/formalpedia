-- Prove2me | Theorems.Thm_GlobalTheory_T_regularSemisimple_centralizer_points_of_commutant_adjoint
-- name    : GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T06:24:13.767909+00:00
-- url     : https://prove2.me/theorems/9082b10d-dd3d-4e14-9919-79dc1318ffc5
-- title:
--   T: regular Semisimple centralizer points of commutant adjoint
-- statement:
--   The T construction uses the regular Semisimple centralizer points of commutant adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleCentralizerPointsOfCommutantAdjStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleCentralizerPointsOfCommutantAdjStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleCentralizerPointsOfCommutantAdj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleCentralizerPointsOfCommutantAdjStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint : GlobalTheory.RegSS.PointsCommutant → GlobalTheory.RegSS.PointsAdjoint → GlobalTheory.RegSS.PointsCentraliser := by sorry
