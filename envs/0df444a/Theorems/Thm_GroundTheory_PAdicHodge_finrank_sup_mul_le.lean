-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_finrank_sup_mul_le
-- name    : GroundTheory.PAdicHodge.finrank_sup_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:15.617058+00:00
-- url     : https://prove2.me/theorems/e1acdc81-b731-4dec-9c44-cd195e9c6fcd
-- title:
--   PAdic Hodge: finrank sup mul le
-- statement:
--   The PAdic Hodge construction uses the finrank sup mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L175-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L175-L185

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

theorem GroundTheory.PAdicHodge.finrank_sup_mul_le {k X Y : IntermediateField B₀ Ω} (hX : k ≤ X) (hY : k ≤ Y) :
    finrank B₀ ↥(X ⊔ Y) * finrank B₀ k ≤ finrank B₀ X * finrank B₀ Y := by sorry
