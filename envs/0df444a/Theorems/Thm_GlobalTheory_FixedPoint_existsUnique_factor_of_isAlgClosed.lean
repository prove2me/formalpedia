-- Prove2me | Theorems.Thm_GlobalTheory_FixedPoint_existsUnique_factor_of_isAlgClosed
-- name    : GlobalTheory.FixedPoint.existsUnique_factor_of_isAlgClosed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:00.061117+00:00
-- url     : https://prove2.me/theorems/2e0da724-d49f-505f-9345-9b4d8d10d870
-- title:
--   Fixed Point: exists Unique factor of is Alg Closed
-- statement:
--   The Fixed Point construction uses the exists Unique factor of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L86-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K₀ K₁ L : Type u} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]

theorem GlobalTheory.FixedPoint.existsUnique_factor_of_isAlgClosed [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of L) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L, Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ x = x) :
    ∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, L) ≫ y = x := by sorry
