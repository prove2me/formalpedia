-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_value_mem_range
-- name    : GlobalTheory.PrimitiveUnitProduct.value_mem_range
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:26.295169+00:00
-- url     : https://prove2.me/theorems/fe9dcccb-ef64-4ec6-9836-32677b6f60cc
-- title:
--   Primitive Unit Product: value mem range
-- statement:
--   The Primitive Unit Product construction uses the value mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L125-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L125-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.PrimitiveUnitProduct

theorem GlobalTheory.PrimitiveUnitProduct.value_mem_range {K A Ω F : Type} [Field K] [CommRing A] [Algebra K A]
    [Field Ω] [IsAlgClosed Ω] [Field F] [Algebra K Ω] [Algebra K F] [Algebra Ω F]
    [IsScalarTower K Ω F]
    (H : ∀ (L : Type) [Field L] [Algebra K L], IsDomain (L ⊗[K] A)) (ι κ : A →ₐ[K] Ω)
    (u : F ⊗[K] A) (hu : IsUnit u)
    (h : Algebra.TensorProduct.lift (AlgHom.id K F) ((IsScalarTower.toAlgHom K Ω F).comp κ)
        (fun _ _ => Commute.all _ _) u = 1) :
    ∃ c : Ω, algebraMap Ω F c =
      Algebra.TensorProduct.lift (AlgHom.id K F) ((IsScalarTower.toAlgHom K Ω F).comp ι)
        (fun _ _ => Commute.all _ _) u := by sorry
