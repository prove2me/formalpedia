-- Prove2me | Theorems.Thm_GlobalTheory_FieldDescentGen_isUnit_of_surjective
-- name    : GlobalTheory.FieldDescentGen.isUnit_of_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:19:38.194511+00:00
-- url     : https://prove2.me/theorems/20f9a274-040e-4cc1-b2d2-bffc6154985f
-- title:
--   Field Descent Gen: is Unit of surjective
-- statement:
--   The Field Descent Gen construction uses the is Unit of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LineBundleTrivialIsoDescendField.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LineBundleTrivialIsoDescendField.lean#L58-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveAppTopOfSmoothOfIsProperOfGeometrically
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendField
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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.FieldDescentGen
variable {X₀ X : Scheme.{0}}

theorem GlobalTheory.FieldDescentGen.isUnit_of_surjective (φ : X ⟶ X₀) [Surjective φ] {U : X₀.Opens} {V : X.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ U ≤ V) (a : Γ(X₀, U)) (ha : IsUnit ((φ.appLE U V h).hom a)) : IsUnit a := by sorry
