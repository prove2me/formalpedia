-- Prove2me | Theorems.Thm_GlobalTheory_FixedPoint_value_mem_range
-- name    : GlobalTheory.FixedPoint.value_mem_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:37.811683+00:00
-- url     : https://prove2.me/theorems/0f39ca02-1a86-409b-abdb-56593ab76f41
-- title:
--   Fixed Point: value mem range
-- statement:
--   The Fixed Point construction uses the value mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L115-L122

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

theorem GlobalTheory.FixedPoint.value_mem_range [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of K₁) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x)
    (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Z, U)) :
    ((Scheme.ΓSpecIso (.of K₁)).hom (x.appLE U ⊤ h f) : K₁) ∈ Set.range (algebraMap K₀ K₁) := by sorry
