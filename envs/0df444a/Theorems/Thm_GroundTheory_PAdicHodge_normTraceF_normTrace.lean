-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTraceF_normTrace
-- name    : GroundTheory.PAdicHodge.normTraceF_normTrace
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:17.691639+00:00
-- url     : https://prove2.me/theorems/d767c1b1-ec37-4d77-a703-915c42bade39
-- title:
--   PAdic Hodge: norm Trace F norm Trace
-- statement:
--   The PAdic Hodge construction uses the norm Trace F norm Trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L94-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L94-L122

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CharZero F] [Algebra.IsIntegral F Ω]

theorem GroundTheory.PAdicHodge.normTraceF_normTrace (E : Type*) [Field E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] [FiniteDimensional F E] (y : Ω) :
    normTraceF F (normTrace E y) = normTraceF F y := by sorry
