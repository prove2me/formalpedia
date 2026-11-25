-- Prove2me | Theorems.Thm_GlobalTheory_TorusLift_isMonHom_pullbackComp
-- name    : GlobalTheory.TorusLift.isMonHom_pullbackComp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:41.282219+00:00
-- url     : https://prove2.me/theorems/77876c83-3a7b-4a71-9d95-fe30c4873167
-- title:
--   Torus Lift: is Mon Hom pullback Comp
-- statement:
--   The Torus Lift construction uses the is Mon Hom pullback Comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PreimageEqTopOfSurjective.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PreimageEqTopOfSurjective.lean#L76-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PreimageEqTopOfSurjective
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
open GlobalTheory GlobalTheory.TorusLift
variable {S S' S'' : Scheme.{0}}

theorem GlobalTheory.TorusLift.isMonHom_pullbackComp (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsMonHom (M := (Over.pullback (s ≫ p)).obj G)
      (N := (Over.pullback s).obj ((Over.pullback p).obj G))
      ((Over.pullbackComp s p).hom.app G) := by sorry
