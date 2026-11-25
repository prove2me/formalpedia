-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_mem_nPlusU
-- name    : GroundTheory.Automorphic.HarishChandra.mul_mem_nPlusU
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:42.497168+00:00
-- url     : https://prove2.me/theorems/08162db5-ef7b-4130-af60-f58a3c3b1692
-- title:
--   Harish Chandra: mul mem n Plus U
-- statement:
--   The Harish Chandra construction uses the mul mem n Plus U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L197-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L197-L204

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

theorem GroundTheory.Automorphic.HarishChandra.mul_mem_nPlusU (v : U n) {x : U n} (hx : x ∈ nPlusU n) : v * x ∈ nPlusU n := by sorry
