-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_of_mem
-- name    : GroundTheory.PAdicHodge.normTrace_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:37.582433+00:00
-- url     : https://prove2.me/theorems/6b936c60-0206-419d-940e-10df56e4108f
-- title:
--   PAdic Hodge: norm Trace of mem
-- statement:
--   The PAdic Hodge construction uses the norm Trace of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L277-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L277-L278

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

theorem GroundTheory.PAdicHodge.normTrace_of_mem (k : IntermediateField B₀ Ω) {a : Ω} (ha : a ∈ k) : normTrace k a = a := by sorry
