-- Prove2me | Theorems.Thm_GlobalTheory_FixedPoint_fixed_of_factor
-- name    : GlobalTheory.FixedPoint.fixed_of_factor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:29.968021+00:00
-- url     : https://prove2.me/theorems/7d44e837-806a-4011-8d5c-f520f7d2de36
-- title:
--   Fixed Point: fixed of factor
-- statement:
--   The Fixed Point construction uses the fixed of factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L54-L60

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

theorem GlobalTheory.FixedPoint.fixed_of_factor {Z : Scheme.{u}} (y : Spec (.of K₀) ⟶ Z) (s : L ≃ₐ[K₀] L) :
    Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ specAlg(K₀, K₁) ≫ y =
      specAlg(K₁, L) ≫ specAlg(K₀, K₁) ≫ y := by sorry
