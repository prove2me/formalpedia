-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_coeffSum_ne_zero
-- name    : GroundTheory.Automorphic.Parabolic.exists_coeffSum_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:59.838348+00:00
-- url     : https://prove2.me/theorems/16077d5e-d469-54d2-b95a-6c9b6301c052
-- title:
--   Parabolic: exists coeff Sum ne zero
-- statement:
--   The Parabolic construction uses the exists coeff Sum ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L242-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L242-L377

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

theorem GroundTheory.Automorphic.Parabolic.exists_coeffSum_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} {ω : GL (Fin n) F → ℂ} [π.IsIrreducible]
    (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) :
    ∃ K : Subgroup (GL (Fin n) F), IsCompact (K : Set (GL (Fin n) F)) ∧
      IsOpen (K : Set (GL (Fin n) F)) ∧ ∃ f : Module.Dual ℂ V, (∀ k ∈ K, ∀ x, f (π k x) = f x) ∧
        ∃ v ∈ fixedVectors π K, ∃ w, coeffSum π π K f v w ≠ 0 := by sorry
