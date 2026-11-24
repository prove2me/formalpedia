-- Prove2me | Theorems.Thm_GlobalTheory_Serre_exists_eigen_tensor
-- name    : GlobalTheory.Serre.exists_eigen_tensor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:09.731854+00:00
-- url     : https://prove2.me/theorems/387a11b4-1685-4e24-83d7-cf2630146ffd
-- title:
--   Serre: exists eigen tensor
-- statement:
--   The Serre construction uses the exists eigen tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L154-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L154-L179

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

theorem GlobalTheory.Serre.exists_eigen_tensor [Module.Finite O M] [Module.Projective O M]
    {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')]
    [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = algebraMap O R x • l) :
    ∃ s : N ⊗[O'] M →ₗ[R] L ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor L z = algebraMap O' R x • z := by sorry
