-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_classParamCM
-- name    : GlobalTheory.ClassParam.classParamCM
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:13:34.663422+00:00
-- url     : https://prove2.me/theorems/78399781-2b8d-4037-a3cb-7127422a78e1
-- title:
--   Class Param: class Param CM
-- statement:
--   The Class Param construction uses the class Param CM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L902-L907
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L902-L907

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam

theorem GlobalTheory.ClassParam.classParamCM : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.ClassParamCM := by sorry
