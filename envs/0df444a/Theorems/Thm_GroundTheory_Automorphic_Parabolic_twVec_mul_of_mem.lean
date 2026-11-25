-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_twVec_mul_of_mem
-- name    : GroundTheory.Automorphic.Parabolic.twVec_mul_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:15:07.376521+00:00
-- url     : https://prove2.me/theorems/2aa52fa2-6b2d-5398-8f7c-5abc2c9e31fa
-- title:
--   Parabolic: tw Vec mul of mem
-- statement:
--   The Parabolic construction uses the tw Vec mul of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L157-L161

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

theorem GroundTheory.Automorphic.Parabolic.twVec_mul_of_mem {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1) (g : GL (Fin n) F) {k : GL (Fin n) F} (hk : k ∈ K) :
    twVec π ω x (g * k) = twVec π ω x g := by sorry
