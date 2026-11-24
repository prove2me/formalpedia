-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_add
-- name    : GroundTheory.PAdicHodge.normTrace_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:28:56.950815+00:00
-- url     : https://prove2.me/theorems/aecdd5c0-0b99-4abe-959c-b7d618c3617b
-- title:
--   PAdic Hodge: norm Trace add
-- statement:
--   The PAdic Hodge construction uses the norm Trace add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L75-L76

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

theorem GroundTheory.PAdicHodge.normTrace_add (y z : Ω) : normTrace F (y + z) = normTrace F y + normTrace F z := by sorry
