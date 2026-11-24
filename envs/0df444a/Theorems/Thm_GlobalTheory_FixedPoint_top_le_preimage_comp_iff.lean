-- Prove2me | Theorems.Thm_GlobalTheory_FixedPoint_top_le_preimage_comp_iff
-- name    : GlobalTheory.FixedPoint.top_le_preimage_comp_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:27.424201+00:00
-- url     : https://prove2.me/theorems/57889ea9-eb74-4c34-85d7-0a442d1f8303
-- title:
--   Fixed Point: top le preimage comp iff
-- statement:
--   The Fixed Point construction uses the top le preimage comp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L98-L103

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

theorem GlobalTheory.FixedPoint.top_le_preimage_comp_iff {Z : Scheme.{u}} (y : Spec (.of K₀) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ (specAlg(K₀, K₁) ≫ y) ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ U := by sorry
