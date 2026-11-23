-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_finiteDimensional_of_le
-- name    : GroundTheory.PAdicHodge.finiteDimensional_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:53.53381+00:00
-- url     : https://prove2.me/theorems/7fc10d42-fc2c-4d8f-8fc7-82d1f26e9bc0
-- title:
--   PAdic Hodge: finite Dimensional of le
-- statement:
--   The PAdic Hodge construction uses the finite Dimensional of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L194-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L194-L197

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

theorem GroundTheory.PAdicHodge.finiteDimensional_of_le {k E : IntermediateField B₀ Ω} (h : k ≤ E) [FiniteDimensional B₀ E] :
    FiniteDimensional B₀ k := by sorry
