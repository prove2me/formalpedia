-- Prove2me | Theorems.Thm_GlobalTheory_GenericExtend_appLE_inv_eq
-- name    : GlobalTheory.GenericExtend.appLE_inv_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:38.492006+00:00
-- url     : https://prove2.me/theorems/ff41a5e4-eae5-4f08-b63b-3fa4c402b49d
-- title:
--   Generic Extend: app LE inv eq
-- statement:
--   The Generic Extend construction uses the app LE inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L262-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L262-L269

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

theorem GlobalTheory.GenericExtend.appLE_inv_eq {P Q H Z : Scheme.{0}} {J : Q ⟶ P} {φ : H ⟶ P} {k : Z ⟶ H} {ψ : Z ⟶ Q}
    {A : P.Opens} (hW : k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A) {s : Γ(H, φ ⁻¹ᵁ A)ˣ} {τ : Γ(Q, J ⁻¹ᵁ A)ˣ}
    (hu : res le_rfl (pullU k _ s) = res hW (pullU ψ _ τ)) :
    (k.appLE _ _ le_rfl).hom s.val = (ψ.appLE _ _ hW).hom τ.val ∧
      (k.appLE _ _ le_rfl).hom (s⁻¹).val = (ψ.appLE _ _ hW).hom (τ⁻¹).val := by sorry
