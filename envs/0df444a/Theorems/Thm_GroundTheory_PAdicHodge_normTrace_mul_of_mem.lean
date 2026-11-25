-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mul_of_mem
-- name    : GroundTheory.PAdicHodge.normTrace_mul_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:53.107812+00:00
-- url     : https://prove2.me/theorems/1c381669-0c1f-4ff6-83c7-ccf26768e3fc
-- title:
--   PAdic Hodge: norm Trace mul of mem
-- statement:
--   The PAdic Hodge construction uses the norm Trace mul of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L280-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L280-L284

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

theorem GroundTheory.PAdicHodge.normTrace_mul_of_mem [CharZero Ω] [Algebra.IsIntegral B₀ Ω] (k : IntermediateField B₀ Ω)
    {a : Ω} (ha : a ∈ k) (y : Ω) : normTrace k (a * y) = a * normTrace k y := by sorry
