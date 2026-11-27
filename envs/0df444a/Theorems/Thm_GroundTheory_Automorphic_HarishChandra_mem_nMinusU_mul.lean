-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_nMinusU_mul
-- name    : GroundTheory.Automorphic.HarishChandra.mem_nMinusU_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:02.2903+00:00
-- url     : https://prove2.me/theorems/e4ea4808-c3e6-4921-bc5b-9b982443c767
-- title:
--   Harish Chandra: mem n Minus U mul
-- statement:
--   The Harish Chandra construction uses the mem n Minus U mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L206-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L206-L213

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

theorem GroundTheory.Automorphic.HarishChandra.mem_nMinusU_mul {x : U n} (hx : x ∈ nMinusU n) (v : U n) : x * v ∈ nMinusU n := by sorry
