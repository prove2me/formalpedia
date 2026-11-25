-- Prove2me | Theorems.Thm_GlobalTheory_T_thetaPsiRelation_of_pullback_extension_field
-- name    : GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:38:19.974814+00:00
-- url     : https://prove2.me/theorems/98d6c5d4-075e-5785-bb28-91c6097dc133
-- title:
--   T: theta Psi Relation of pullback extension field
-- statement:
--   The T construction uses the theta Psi Relation of pullback extension field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ThetaPsiRelationOfPullbackExtensionFieldStatement.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ThetaPsiRelationOfPullbackExtensionFieldStatement.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ThetaPsiRelationOfPullbackExtensionField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ThetaPsiRelationOfPullbackExtensionFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by sorry
