-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_exists_unit_value
-- name    : GlobalTheory.PrimitiveUnitProduct.exists_unit_value
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:10.532303+00:00
-- url     : https://prove2.me/theorems/c0113693-fb29-4152-b1b2-e00fc9e6a5b0
-- title:
--   Primitive Unit Product: exists unit value
-- statement:
--   The Primitive Unit Product construction uses the exists unit value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L64-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L64-L121

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
variable {K A O F : Type} [Field K] [CommRing A] [Algebra K A] [CommRing O] [IsDomain O]
  [ValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K O] [Algebra K F]
  [IsScalarTower K O F]

theorem GlobalTheory.PrimitiveUnitProduct.exists_unit_value [IsDomain (IsLocalRing.ResidueField O ⊗[K] A)]
    (u v : F ⊗[K] A) (huv : u * v = 1) :
    ∃ c : F, ∀ φ : A →ₐ[K] O, ∃ w : O, IsUnit w ∧
      Algebra.TensorProduct.lift (AlgHom.id K F) ((IsScalarTower.toAlgHom K O F).comp φ)
        (fun _ _ => Commute.all _ _) u = c * algebraMap O F w := by sorry
