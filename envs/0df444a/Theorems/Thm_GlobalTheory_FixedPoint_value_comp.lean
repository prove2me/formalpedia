-- Prove2me | Theorems.Thm_GlobalTheory_FixedPoint_value_comp
-- name    : GlobalTheory.FixedPoint.value_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:37.410085+00:00
-- url     : https://prove2.me/theorems/468e9781-05c5-4200-8a7e-45aaaaf35fe8
-- title:
--   Fixed Point: value comp
-- statement:
--   The Fixed Point construction uses the value comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean#L105-L113

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

theorem GlobalTheory.FixedPoint.value_comp {A B : CommRingCat.{u}} (g : A ⟶ B) {Z : Scheme.{u}} (y : Spec A ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map g ≫ y) ⁻¹ᵁ U) (f : Γ(Z, U)) :
    (Scheme.ΓSpecIso B).hom ((Spec.map g ≫ y).appLE U ⊤ h' f) =
      g ((Scheme.ΓSpecIso A).hom (y.appLE U ⊤ h f)) := by sorry
