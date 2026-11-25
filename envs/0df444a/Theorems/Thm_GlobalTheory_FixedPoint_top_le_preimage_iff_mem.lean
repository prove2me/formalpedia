-- Prove2me | Theorems.Thm_GlobalTheory_FixedPoint_top_le_preimage_iff_mem
-- name    : GlobalTheory.FixedPoint.top_le_preimage_iff_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:55.874284+00:00
-- url     : https://prove2.me/theorems/75f6d01e-7e31-4519-a90c-63aa3321f441
-- title:
--   Fixed Point: top le preimage iff mem
-- statement:
--   The Fixed Point construction uses the top le preimage iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L92-L96

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

theorem GlobalTheory.FixedPoint.top_le_preimage_iff_mem {Z : Scheme.{u}} (x : Spec (.of K₁) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint K₁) ∈ U := by sorry
