-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_finrank_sup_adjoin_simple
-- name    : GroundTheory.PAdicHodge.finrank_sup_adjoin_simple
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:53.094272+00:00
-- url     : https://prove2.me/theorems/4c39158e-73e9-4308-98b9-2c3a6a3acc63
-- title:
--   PAdic Hodge: finrank sup adjoin simple
-- statement:
--   The PAdic Hodge construction uses the finrank sup adjoin simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L187-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L187-L192

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

theorem GroundTheory.PAdicHodge.finrank_sup_adjoin_simple (F : IntermediateField B₀ Ω) {z : Ω} (hz : IsIntegral F z) :
    finrank B₀ ↥(F ⊔ adjoin B₀ {z}) = finrank B₀ F * (minpoly F z).natDegree := by sorry
