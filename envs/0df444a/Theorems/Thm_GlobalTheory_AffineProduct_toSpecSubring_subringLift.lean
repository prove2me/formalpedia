-- Prove2me | Theorems.Thm_GlobalTheory_AffineProduct_toSpecSubring_subringLift
-- name    : GlobalTheory.AffineProduct.toSpecSubring_subringLift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:55:02.408026+00:00
-- url     : https://prove2.me/theorems/a9129e2d-a094-45b7-b07e-bfddd76ed457
-- title:
--   Affine Product: to Spec Subring subring Lift
-- statement:
--   The Affine Product construction uses the to Spec Subring subring Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineAndGeneratedOfWideProduct.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineAndGeneratedOfWideProduct.lean#L20-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineAndGeneratedOfWideProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AffineProduct

theorem GlobalTheory.AffineProduct.toSpecSubring_subringLift {Y X : Scheme.{0}} [IsAffine X] (B : Subring Γ(Y, ⊤))
    (f : Y ⟶ X) (h : ∀ a, f.appTop.hom a ∈ B) :
    toSpecSubring B ≫ subringLift B f h = f := by sorry
