-- Prove2me | Theorems.Thm_GlobalTheory_AbPackage_exists_rigidified_sym
-- name    : GlobalTheory.AbPackage.exists_rigidified_sym
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:35:45.187235+00:00
-- url     : https://prove2.me/theorems/8e157f2b-0288-470f-bdfb-a7f8c97f2453
-- title:
--   Ab Package: exists rigidified sym
-- statement:
--   The Ab Package construction uses the exists rigidified sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AbelianSchemeCubicalBundleExistsAndMaps.lean#L37-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AbelianSchemeCubicalBundleExistsAndMaps.lean#L37-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_IsCPPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AbelianSchemeCubicalBundleExistsAndMaps
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
open GlobalTheory GlobalTheory.AbPackage
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
omit [IsCommMonObj B]

theorem GlobalTheory.AbPackage.exists_rigidified_sym {L : LB B.left} (hL : L.IsLB)
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (eSec B)) (LB.oneGen L) := by sorry
