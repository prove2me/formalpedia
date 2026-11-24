-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UQ_cInt_spec
-- name    : GlobalTheory.UnitLemma.UQ.cInt_spec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:19.842557+00:00
-- url     : https://prove2.me/theorems/a81911e1-6eec-4511-b8a7-e582dddd32d7
-- title:
--   UQ: c Int spec
-- statement:
--   The UQ construction uses the c Int spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuation.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuation.lean#L20-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.UQ.cInt_spec (K : UQ) (x : K.O) :
    algebraMap K.O K.E (K.cInt x) = K.c (algebraMap K.O K.E x) := by sorry
