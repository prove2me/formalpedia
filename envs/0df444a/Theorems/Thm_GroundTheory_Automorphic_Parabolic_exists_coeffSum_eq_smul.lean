-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_coeffSum_eq_smul
-- name    : GroundTheory.Automorphic.Parabolic.exists_coeffSum_eq_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:10.924717+00:00
-- url     : https://prove2.me/theorems/28b6e601-2248-5b67-9041-ea2182209401
-- title:
--   Parabolic: exists coeff Sum eq smul
-- statement:
--   The Parabolic construction uses the exists coeff Sum eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingCoeff.lean#L203-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingCoeff.lean#L203-L212

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
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
open Function
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {v : V} {ω : GL (Fin n) F → ℂ}

theorem GroundTheory.Automorphic.Parabolic.exists_coeffSum_eq_smul [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hωπ : HasCentralChar π ω)
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hv : v ∈ fixedVectors π K) :
    ∃ c : ℂ, ∀ w, coeffSum π π K f v w = c • w := by sorry
