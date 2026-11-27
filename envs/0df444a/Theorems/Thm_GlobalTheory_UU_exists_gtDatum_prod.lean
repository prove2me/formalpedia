-- Prove2me | Theorems.Thm_GlobalTheory_UU_exists_gtDatum_prod
-- name    : GlobalTheory.UU.exists_gtDatum_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:25:39.342802+00:00
-- url     : https://prove2.me/theorems/db5eb3ef-3930-57e2-8df8-05e5f2abe0b5
-- title:
--   UU: exists gt Datum prod
-- statement:
--   The UU construction uses the exists gt Datum prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/LocalTrivialization/LocTrivOfRetraction.lean#L131-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/LocalTrivialization/LocTrivOfRetraction.lean#L131-L142

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Statements_LocalTrivialization_LocTrivOfRetraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem GlobalTheory.UU.exists_gtDatum_prod [Module.Free ℤ X] [Module.Finite ℤ X] (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ (O : X → RigLB A) (h₁ : _) (h₂ : _) (h₃ : _)
      (Dat : (SplitExt.mk A hA X O h₁ h₂ h₃).GtDatum (splitTorus S X ⊗ A)) (Q : TQ (splitTorus S X ⊗ A) X),
      Q.i = Dat.i := by sorry
