-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hasUpper_notUpper_add
-- name    : GroundTheory.Automorphic.HarishChandra.hasUpper_notUpper_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:08:14.641473+00:00
-- url     : https://prove2.me/theorems/c804db5a-8cfb-4ae8-b9d2-4082fda57652
-- title:
--   Harish Chandra: has Upper not Upper add
-- statement:
--   The Harish Chandra construction uses the has Upper not Upper add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L292-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L292-L298

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

theorem GroundTheory.Automorphic.HarishChandra.hasUpper_notUpper_add {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsUpper a)
    (hdeg : 1 ≤ m'.degree) : HasUpper (notUpper m + m') := by sorry
