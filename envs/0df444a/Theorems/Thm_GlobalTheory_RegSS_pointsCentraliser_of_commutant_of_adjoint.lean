-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_pointsCentraliser_of_commutant_of_adjoint
-- name    : GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T06:21:59.98763+00:00
-- url     : https://prove2.me/theorems/327e5854-9896-5eef-bf8d-fbc6ab4b4dc0
-- title:
--   Reg SS: points Centraliser of commutant of adjoint
-- statement:
--   The Reg SS construction uses the points Centraliser of commutant of adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleCentralizerPointsOfCommutantAdj.lean#L22-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleCentralizerPointsOfCommutantAdj.lean#L22-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleCentralizerPointsOfCommutantAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS

theorem GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint :
    PointsCommutant → PointsAdjoint → PointsCentraliser := by sorry
