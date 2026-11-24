-- Prove2me | Theorems.Thm_GlobalTheory_Serre_exists_elem_of_unramified
-- name    : GlobalTheory.Serre.exists_elem_of_unramified
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:13.015102+00:00
-- url     : https://prove2.me/theorems/e473f362-389f-43fa-b1fa-734ca7dfe9a1
-- title:
--   Serre: exists elem of unramified
-- statement:
--   The Serre construction uses the exists elem of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L24-L37

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

theorem GlobalTheory.Serre.exists_elem_of_unramified {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A] (χ : A →ₐ[R] R) :
    ∃ e : A, χ e = 1 ∧ ∀ x, x * e = χ x • e := by sorry
