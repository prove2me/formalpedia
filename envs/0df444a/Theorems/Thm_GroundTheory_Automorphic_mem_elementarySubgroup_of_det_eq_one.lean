-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_elementarySubgroup_of_det_eq_one
-- name    : GroundTheory.Automorphic.mem_elementarySubgroup_of_det_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:48.243926+00:00
-- url     : https://prove2.me/theorems/bbc1cb44-db5d-5dee-bdcc-cb8cf80f8ab4
-- title:
--   Automorphic: mem elementary Subgroup of det eq one
-- statement:
--   The Automorphic construction uses the mem elementary Subgroup of det eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L146-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L146-L173

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F : Type*} [Field F]

theorem GroundTheory.Automorphic.mem_elementarySubgroup_of_det_eq_one {g : GL n F}
    (hg : Matrix.GeneralLinearGroup.det g = 1) : g ∈ elementarySubgroup n F := by sorry
