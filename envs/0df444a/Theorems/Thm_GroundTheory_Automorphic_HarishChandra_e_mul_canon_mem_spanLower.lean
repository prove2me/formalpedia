-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_canon_mem_spanLower
-- name    : GroundTheory.Automorphic.HarishChandra.e_mul_canon_mem_spanLower
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:07:39.944528+00:00
-- url     : https://prove2.me/theorems/0f16b974-6b59-4c48-99ef-b041e97d157f
-- title:
--   Harish Chandra: e mul canon mem span Lower
-- statement:
--   The Harish Chandra construction uses the e mul canon mem span Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L341-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L341-L362

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

theorem GroundTheory.Automorphic.HarishChandra.e_mul_canon_mem_spanLower (m : Fin n × Fin n →₀ ℕ) {a : Fin n × Fin n} (ha : IsLower a) :
    e a * canon m ∈ spanLower n := by sorry
