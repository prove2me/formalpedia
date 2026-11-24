-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_smul
-- name    : GroundTheory.PAdicHodge.normTrace_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:25.302489+00:00
-- url     : https://prove2.me/theorems/2aff1210-4c3b-4190-8fd8-4f2bcd129735
-- title:
--   PAdic Hodge: norm Trace smul
-- statement:
--   The PAdic Hodge construction uses the norm Trace smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L83-L84

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

theorem GroundTheory.PAdicHodge.normTrace_smul (a : F) (y : Ω) : normTrace F (a • y) = a • normTrace F y := by sorry
