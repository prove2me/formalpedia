-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_pointsEquiv_eq_iff
-- name    : GlobalTheory.CartierDual.pointsEquiv_eq_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:58.391436+00:00
-- url     : https://prove2.me/theorems/719bf433-c912-4443-acdf-9ac135de1185
-- title:
--   Cartier Dual: points Equiv eq iff
-- statement:
--   The Cartier Dual construction uses the points Equiv eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L809-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L809-L812

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open GlobalTheory.CartierDual
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Module.Finite R C] [Module.Projective R C]
variable {A : Type*} [CommSemiring A] [Algebra R A]

theorem GlobalTheory.CartierDual.pointsEquiv_eq_iff (f : CartierDual R C →ₐ[R] A) (x : A ⊗[R] C) :
    (pointsEquiv R C A f).val = x ↔ ∀ φ, tensorToHom R A C x φ = f φ := by sorry
