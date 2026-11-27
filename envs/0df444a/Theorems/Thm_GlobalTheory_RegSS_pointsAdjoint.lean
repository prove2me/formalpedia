-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_pointsAdjoint
-- name    : GlobalTheory.RegSS.pointsAdjoint
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T06:22:13.74149+00:00
-- url     : https://prove2.me/theorems/a2f60f7f-002c-4f3f-bb34-1c7764c07e5a
-- title:
--   Reg SS: points Adjoint
-- statement:
--   The Reg SS construction uses the points Adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorInvolutionAdjoint.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorInvolutionAdjoint.lean#L17-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorInvolutionAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS

theorem GlobalTheory.RegSS.pointsAdjoint : PointsAdjoint := by sorry
