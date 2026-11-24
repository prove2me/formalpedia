-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq
-- name    : GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_of_matrixCoeff_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:41.603918+00:00
-- url     : https://prove2.me/theorems/06d45a63-2977-4414-ae8e-18d8279b37ed
-- title:
--   Restricted Tensor: nonempty equiv of matrix Coeff eq
-- statement:
--   The Restricted Tensor construction uses the nonempty equiv of matrix Coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L90-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L90-L138

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set
open GroundTheory.Automorphic.RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_of_matrixCoeff_eq {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    [ρ.IsIrreducible] [σ.IsIrreducible] {v : V} {l : Module.Dual ℂ V} {w : W}
    {m : Module.Dual ℂ W} (h : ∀ g, l (ρ g v) = m (σ g w)) (hne : ∃ g, l (ρ g v) ≠ 0) :
    Nonempty (ρ.Equiv σ) := by sorry
