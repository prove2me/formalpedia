-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_finite_support_normSq_twVec
-- name    : GroundTheory.Automorphic.Parabolic.finite_support_normSq_twVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:36.655699+00:00
-- url     : https://prove2.me/theorems/3a5dad7e-6820-5fbd-b966-94b3478fc34c
-- title:
--   Parabolic: finite support norm Sq tw Vec
-- statement:
--   The Parabolic construction uses the finite support norm Sq tw Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L223-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L223-L229

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
omit hωπ hv

theorem GroundTheory.Automorphic.Parabolic.finite_support_normSq_twVec (x : V) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => ‖f (twVec π ω x q.out)‖ ^ 2 := by sorry
