-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_unit_on_product_eq_one
-- name    : GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:00.202797+00:00
-- url     : https://prove2.me/theorems/703aac32-d542-4452-b99c-598cb4ef6a7d
-- title:
--   Primitive Unit Product: unit on product eq one
-- statement:
--   The Primitive Unit Product construction uses the unit on product eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L258-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L258-L365

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

theorem GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one {K : Type} [Field K] [IsAlgClosed K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [GeometricallyIntegral f]
    (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ f = 𝟙 _) (a₁ a₂ : X ⟶ pullback f f)
    (h₁₁ : a₁ ≫ pullback.fst f f = 𝟙 X) (h₁₂ : a₁ ≫ pullback.snd f f = f ≫ e)
    (h₂₁ : a₂ ≫ pullback.fst f f = f ≫ e) (h₂₂ : a₂ ≫ pullback.snd f f = 𝟙 X)
    (u : Γ(pullback f f, ⊤)) (hu : IsUnit u) (hu₁ : a₁.appTop.hom u = 1)
    (hu₂ : a₂.appTop.hom u = 1) : u = 1 := by sorry
