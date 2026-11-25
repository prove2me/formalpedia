-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_eq_zero_of_quotSum_normSq
-- name    : GroundTheory.Automorphic.Parabolic.apply_eq_zero_of_quotSum_normSq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:09:30.954357+00:00
-- url     : https://prove2.me/theorems/db77da9c-e2b7-56f8-afa3-85f5e025567f
-- title:
--   Parabolic: apply eq zero of quot Sum norm Sq
-- statement:
--   The Parabolic construction uses the apply eq zero of quot Sum norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L231-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L231-L238

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
  {ω : GL (Fin n) F → ℂ}
variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) {v : V}
  (hv : v ≠ 0) {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F)))
  {f : Module.Dual ℂ V} (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x)
include hπ hsc hωπ hv hKo hf

theorem GroundTheory.Automorphic.Parabolic.apply_eq_zero_of_quotSum_normSq {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1)
    (h0 : quotSum (centerSup K) (fun g => ‖f (twVec π ω x g)‖ ^ 2) = 0) : f x = 0 := by sorry
