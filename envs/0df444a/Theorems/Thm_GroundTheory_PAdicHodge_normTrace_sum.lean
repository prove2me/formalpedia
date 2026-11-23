-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sum
-- name    : GroundTheory.PAdicHodge.normTrace_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:58.807795+00:00
-- url     : https://prove2.me/theorems/7db200f2-5cc6-43e4-89c0-69eec1cf1178
-- title:
--   PAdic Hodge: norm Trace sum
-- statement:
--   The PAdic Hodge construction uses the norm Trace sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L86-L88

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

theorem GroundTheory.PAdicHodge.normTrace_sum {ι : Type*} (s : Finset ι) (f : ι → Ω) :
    normTrace F (∑ i ∈ s, f i) = ∑ i ∈ s, normTrace F (f i) := by sorry
