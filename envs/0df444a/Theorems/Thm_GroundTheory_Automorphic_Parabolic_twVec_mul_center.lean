-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_twVec_mul_center
-- name    : GroundTheory.Automorphic.Parabolic.twVec_mul_center
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:16:00.776459+00:00
-- url     : https://prove2.me/theorems/04b74cd4-28a3-58f7-b3cf-471c1ede6ca3
-- title:
--   Parabolic: tw Vec mul center
-- statement:
--   The Parabolic construction uses the tw Vec mul center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L143-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L143-L154

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology ComplexConjugate
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V}
variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Parabolic.twVec_mul_center (x : V) (g : GL (Fin n) F) {z : GL (Fin n) F}
    (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    twVec π ω x (g * z) = (ω z / (‖ω z‖ : ℂ)) • twVec π ω x g := by sorry
