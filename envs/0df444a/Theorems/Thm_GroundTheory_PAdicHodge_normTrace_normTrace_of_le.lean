-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_normTrace_of_le
-- name    : GroundTheory.PAdicHodge.normTrace_normTrace_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:07.744804+00:00
-- url     : https://prove2.me/theorems/9126e1f9-5c18-43d1-8083-268079d6410e
-- title:
--   PAdic Hodge: norm Trace norm Trace of le
-- statement:
--   The PAdic Hodge construction uses the norm Trace norm Trace of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L263-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L263-L272

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
variable {B₀ Ω : Type*} [Field B₀] [Field Ω] [Algebra B₀ Ω]

theorem GroundTheory.PAdicHodge.normTrace_normTrace_of_le [CharZero Ω] [Algebra.IsIntegral B₀ Ω]
    {k E : IntermediateField B₀ Ω} (h : k ≤ E) [FiniteDimensional B₀ E] (y : Ω) :
    normTrace k (normTrace E y) = normTrace k y := by sorry
