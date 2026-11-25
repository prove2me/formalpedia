-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_isUpper_of_mem_support
-- name    : GroundTheory.Automorphic.HarishChandra.isUpper_of_mem_support
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:47.015891+00:00
-- url     : https://prove2.me/theorems/69110d7f-0fc7-4865-bdcf-c7ec7c97c75a
-- title:
--   Harish Chandra: is Upper of mem support
-- statement:
--   The Harish Chandra construction uses the is Upper of mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L237-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L237-L240

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

theorem GroundTheory.Automorphic.HarishChandra.isUpper_of_mem_support {P : Fin n × Fin n → Prop} {m : Fin n × Fin n →₀ ℕ}
    (hm : ∀ a ∈ m.support, P a) {a : Fin n × Fin n} (ha : ¬ P a) : m a = 0 := by sorry
