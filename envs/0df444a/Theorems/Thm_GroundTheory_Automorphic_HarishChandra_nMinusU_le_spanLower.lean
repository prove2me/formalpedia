-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_nMinusU_le_spanLower
-- name    : GroundTheory.Automorphic.HarishChandra.nMinusU_le_spanLower
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:58.720038+00:00
-- url     : https://prove2.me/theorems/6d0cf3c3-501a-411b-900c-9bf2d6c2ba8e
-- title:
--   Harish Chandra: n Minus U le span Lower
-- statement:
--   The Harish Chandra construction uses the n Minus U le span Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L381-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L381-L390

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
open scoped IsMulCommutative

theorem GroundTheory.Automorphic.HarishChandra.nMinusU_le_spanLower : nMinusU n ≤ spanLower n := by sorry
