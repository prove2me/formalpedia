-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_unit_eq_one
-- name    : GlobalTheory.PrimitiveUnitProduct.unit_eq_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:18.794807+00:00
-- url     : https://prove2.me/theorems/9f121a8b-f937-47e6-8e40-8596972319b8
-- title:
--   Primitive Unit Product: unit eq one
-- statement:
--   The Primitive Unit Product construction uses the unit eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L180-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L180-L248

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

theorem GlobalTheory.PrimitiveUnitProduct.unit_eq_one {K A : Type} [Field K] [CommRing A] [Algebra K A] [IsDomain A]
    (H : ∀ (L : Type) [Field L] [Algebra K L], IsDomain (L ⊗[K] A)) (ε : A →ₐ[K] K)
    (u : A ⊗[K] A) (hu : IsUnit u) (p₁ p₂ : A ⊗[K] A →+* A)
    (hp₁ : ∀ a b, p₁ (a ⊗ₜ b) = a * algebraMap K A (ε b))
    (hp₂ : ∀ a b, p₂ (a ⊗ₜ b) = algebraMap K A (ε a) * b)
    (h₁ : p₁ u = 1) (h₂ : p₂ u = 1) : u = 1 := by sorry
