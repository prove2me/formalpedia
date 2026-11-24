-- Prove2me | Theorems.Thm_GlobalTheory_Serre_exists_eigen_of_projective
-- name    : GlobalTheory.Serre.exists_eigen_of_projective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:34.7819+00:00
-- url     : https://prove2.me/theorems/5bd5f7aa-7245-4777-87bd-8662b81df698
-- title:
--   Serre: exists eigen of projective
-- statement:
--   The Serre construction uses the exists eigen of projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L107-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L107-L152

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
omit [Algebra O R]

theorem GlobalTheory.Serre.exists_eigen_of_projective (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [SMulCommClass O R N] [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (τ : O → R) (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hlin : ∀ (x : O) n, i (x • n) = x • i n)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = τ x • l) :
    ∃ j : N ⊗[O] M →ₗ[R] L ⊗[O] M, (∀ n m, j (n ⊗ₜ m) = i n ⊗ₜ m) ∧ Function.Injective j ∧
      ∀ z, z ∈ LinearMap.range j ↔ ∀ x : O, x • z = τ x • z := by sorry
