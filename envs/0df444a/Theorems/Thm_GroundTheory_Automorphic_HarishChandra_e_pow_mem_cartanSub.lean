-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_pow_mem_cartanSub
-- name    : GroundTheory.Automorphic.HarishChandra.e_pow_mem_cartanSub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:20.885058+00:00
-- url     : https://prove2.me/theorems/d30099a7-c9c4-5f46-9177-a4358c7b6525
-- title:
--   Harish Chandra: e pow mem cartan Sub
-- statement:
--   The Harish Chandra construction uses the e pow mem cartan Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L155-L156

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

theorem GroundTheory.Automorphic.HarishChandra.e_pow_mem_cartanSub (i : Fin n) (k : ℕ) : e (n := n) (i, i) ^ k ∈ cartanSub n := by sorry
