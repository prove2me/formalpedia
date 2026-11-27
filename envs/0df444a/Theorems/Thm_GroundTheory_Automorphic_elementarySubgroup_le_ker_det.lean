-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_elementarySubgroup_le_ker_det
-- name    : GroundTheory.Automorphic.elementarySubgroup_le_ker_det
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:52.200226+00:00
-- url     : https://prove2.me/theorems/0e36cd61-457b-46e1-ab6a-b58cbc7aa3b6
-- title:
--   Automorphic: elementary Subgroup le ker det
-- statement:
--   The Automorphic construction uses the elementary Subgroup le ker det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L32-L38

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
variable (n) (R : Type*) [CommRing R]
variable {n R}

theorem GroundTheory.Automorphic.elementarySubgroup_le_ker_det :
    elementarySubgroup n R ≤ (Matrix.GeneralLinearGroup.det : GL n R →* Rˣ).ker := by sorry
