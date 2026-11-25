-- Prove2me | Theorems.Thm_GlobalTheory_GenericExtend_extAt_of_generic
-- name    : GlobalTheory.GenericExtend.extAt_of_generic
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:01:39.296606+00:00
-- url     : https://prove2.me/theorems/986f3162-74ee-4ba7-8fa4-5f5fe723ac49
-- title:
--   Generic Extend: ext At of generic
-- statement:
--   The Generic Extend construction uses the ext At of generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L109-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L109-L157

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

theorem GlobalTheory.GenericExtend.extAt_of_generic {Q Y H Z : Scheme.{0}} [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]
    [IsReduced Q] (J : Q ⟶ Y) [IsPreimmersion J] (φ : H ⟶ Y) [IsPreimmersion φ] (k : Z ⟶ H)
    (ψ : Z ⟶ Q) (w : ψ ≫ J = k ≫ φ) (W : Y.Opens) (f : Γ(Q, J ⁻¹ᵁ W)) (s : Γ(H, φ ⁻¹ᵁ W))
    {O : Z.Opens} (h₁ : O ≤ k ⁻¹ᵁ φ ⁻¹ᵁ W) (h₂ : O ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ W)
    (hs : (k.appLE _ O h₁).hom s = (ψ.appLE _ O h₂).hom f) (z : Z) (hz : z ∈ O) (h : H)
    (hh : φ h ∈ W) (hg : ∀ y, y ⤳ φ h → φ (k z) ⤳ y) : ExtAt J W f (φ h) := by sorry
