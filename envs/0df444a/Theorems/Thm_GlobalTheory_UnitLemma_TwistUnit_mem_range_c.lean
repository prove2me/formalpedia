-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_TwistUnit_mem_range_c
-- name    : GlobalTheory.UnitLemma.TwistUnit.mem_range_c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:22.510922+00:00
-- url     : https://prove2.me/theorems/b4ae70d4-206f-4f7c-aa94-39de77ae0c4e
-- title:
--   Twist Unit: mem range c
-- statement:
--   The Twist Unit construction uses the mem range c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L100-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemAdjoinOfMulEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TwistUnit
open GlobalTheory.UnitLemma Polynomial
variable {K : UQ}

theorem GlobalTheory.UnitLemma.TwistUnit.mem_range_c (e : K.E) : K.c e ∈ (algebraMap K.O K.E).range ↔ e ∈ (algebraMap K.O K.E).range := by sorry
