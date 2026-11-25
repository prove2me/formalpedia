-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mul_e_mem_spanUpper
-- name    : GroundTheory.Automorphic.HarishChandra.canon_mul_e_mem_spanUpper
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:07:53.770888+00:00
-- url     : https://prove2.me/theorems/969680f4-fa14-4852-8433-23685f2446ab
-- title:
--   Harish Chandra: canon mul e mem span Upper
-- statement:
--   The Harish Chandra construction uses the canon mul e mem span Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L314-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L314-L339

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

theorem GroundTheory.Automorphic.HarishChandra.canon_mul_e_mem_spanUpper (m : Fin n × Fin n →₀ ℕ) {a : Fin n × Fin n} (ha : IsUpper a) :
    canon m * e a ∈ spanUpper n := by sorry
