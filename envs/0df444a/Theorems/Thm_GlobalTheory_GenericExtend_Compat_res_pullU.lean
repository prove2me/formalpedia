-- Prove2me | Theorems.Thm_GlobalTheory_GenericExtend_Compat_res_pullU
-- name    : GlobalTheory.GenericExtend.Compat.res_pullU
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:10.091817+00:00
-- url     : https://prove2.me/theorems/5fb1dc8d-e2cf-473d-b5d4-dde63f095ba1
-- title:
--   Compat: res pull U
-- statement:
--   The Compat construction uses the res pull U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L205-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L205-L221

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend

theorem GlobalTheory.GenericExtend.Compat.res_pullU {Q Y H Z : Scheme.{0}} {N : LB Y} {J : Q ⟶ Y}
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {φ : H ⟶ Y} {k : Z ⟶ H} {ψ : Z ⟶ Q}
    (hψ : ψ ≫ J = k ≫ φ) (hW : ∀ A : Y.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A) (a b : N.ι) :
    res (inf_le_left : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ _)
      (res (hW _) (pullU ψ _ (τ a))) =
      res (le_rfl : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ k ⁻¹ᵁ φ ⁻¹ᵁ (N.U a ⊓ N.U b))
        (pullU k _ (pullU φ _ (N.g a b))) *
        res (inf_le_right : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ _)
          (res (hW _) (pullU ψ _ (τ b))) := by sorry
