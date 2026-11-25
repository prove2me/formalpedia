-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mul_self_unit
-- name    : GroundTheory.Automorphic.Parabolic.conj_mul_self_unit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:09:36.540809+00:00
-- url     : https://prove2.me/theorems/c0e6415f-01a7-55bd-936c-cbe0c14180a9
-- title:
--   Parabolic: conj mul self unit
-- statement:
--   The Parabolic construction uses the conj mul self unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L178-L184

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

theorem GroundTheory.Automorphic.Parabolic.conj_mul_self_unit {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    conj (ω z / (‖ω z‖ : ℂ)) * (ω z / (‖ω z‖ : ℂ)) = 1 := by sorry
