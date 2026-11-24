-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_exists_primitive
-- name    : GlobalTheory.PrimitiveUnitProduct.exists_primitive
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:32.054039+00:00
-- url     : https://prove2.me/theorems/dc180921-e27c-4084-98fa-b86cc50557b1
-- title:
--   Primitive Unit Product: exists primitive
-- statement:
--   The Primitive Unit Product construction uses the exists primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L12-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitOnProductEqOne.lean#L12-L62

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

theorem GlobalTheory.PrimitiveUnitProduct.exists_primitive (t : F ⊗[K] A) (ht : t ≠ 0) :
    ∃ (c : F) (t' : O ⊗[K] A),
      t = (c ⊗ₜ[K] (1 : A)) *
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O F) (AlgHom.id K A) t' ∧
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
        (AlgHom.id K A) t' ≠ 0 := by sorry
