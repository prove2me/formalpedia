-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_sub_far_of_isClosed
-- name    : GroundTheory.PAdicHodge.exists_sub_far_of_isClosed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:22.76151+00:00
-- url     : https://prove2.me/theorems/b9098ccc-5ba1-46a5-b93a-f62ec4a8f4a7
-- title:
--   PAdic Hodge: exists sub far of is Closed
-- statement:
--   The PAdic Hodge construction uses the exists sub far of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean#L13-L27

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]
omit [IsUltrametricDist k] [IsUltrametricDist E]

theorem GroundTheory.PAdicHodge.exists_sub_far_of_isClosed {U : Submodule k E} (hU : IsClosed (U : Set E)) {x : E}
    (hx : x ∉ U) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ u ∈ U, ∀ u' ∈ U, s * ‖x - u‖ ≤ ‖x - u - u'‖ := by sorry
