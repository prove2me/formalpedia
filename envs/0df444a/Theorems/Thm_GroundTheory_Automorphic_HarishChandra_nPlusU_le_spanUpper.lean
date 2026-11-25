-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_nPlusU_le_spanUpper
-- name    : GroundTheory.Automorphic.HarishChandra.nPlusU_le_spanUpper
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:34.310797+00:00
-- url     : https://prove2.me/theorems/55064d44-7ab6-4450-8795-b9586dfa1432
-- title:
--   Harish Chandra: n Plus U le span Upper
-- statement:
--   The Harish Chandra construction uses the n Plus U le span Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L370-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L370-L379

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

theorem GroundTheory.Automorphic.HarishChandra.nPlusU_le_spanUpper : nPlusU n ≤ spanUpper n := by sorry
