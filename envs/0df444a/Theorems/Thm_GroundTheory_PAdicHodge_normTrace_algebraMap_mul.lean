-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_algebraMap_mul
-- name    : GroundTheory.PAdicHodge.normTrace_algebraMap_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:08.0448+00:00
-- url     : https://prove2.me/theorems/aace519f-398c-44bb-8adc-b4d6a760935d
-- title:
--   PAdic Hodge: norm Trace algebra Map mul
-- statement:
--   The PAdic Hodge construction uses the norm Trace algebra Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L90-L92

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

theorem GroundTheory.PAdicHodge.normTrace_algebraMap_mul (a : F) (y : Ω) :
    normTrace F (algebraMap F Ω a * y) = algebraMap F Ω a * normTrace F y := by sorry
