-- Prove2me | Theorems.Thm_GlobalTheory_Serre_exists_eigen_of_unramified
-- name    : GlobalTheory.Serre.exists_eigen_of_unramified
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:04.380399+00:00
-- url     : https://prove2.me/theorems/fb7d8204-98e4-40e6-8af7-bdabb3908071
-- title:
--   Serre: exists eigen of unramified
-- statement:
--   The Serre construction uses the exists eigen of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L41-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L41-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]
variable {M : Type*} [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem GlobalTheory.Serre.exists_eigen_of_unramified (N : Type*) [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')] :
    ∃ s : N ⊗[O'] M →ₗ[R] N ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor N z = algebraMap O' R x • z := by sorry
