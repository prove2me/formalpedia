-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_le_norm_smul_add_of_far
-- name    : GroundTheory.PAdicHodge.le_norm_smul_add_of_far
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:28.436827+00:00
-- url     : https://prove2.me/theorems/445a9151-09e2-4abc-84b9-6738464cff0b
-- title:
--   PAdic Hodge: le norm smul add of far
-- statement:
--   The PAdic Hodge construction uses the le norm smul add of far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean#L31-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean#L31-L49

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
omit [IsUltrametricDist k]

theorem GroundTheory.PAdicHodge.le_norm_smul_add_of_far {U : Submodule k E} {w : E} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hw : ∀ u' ∈ U, s * ‖w‖ ≤ ‖w - u'‖) (a : k) {u : E} (hu : u ∈ U) :
    s * ‖a • w‖ ≤ ‖a • w + u‖ ∧ s * ‖u‖ ≤ ‖a • w + u‖ := by sorry
