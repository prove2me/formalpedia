-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwo_exists_sec_finsum
-- name    : GlobalTheory.WeightTwo.exists_sec_finsum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:01.349415+00:00
-- url     : https://prove2.me/theorems/b1ec16da-529f-46d3-b5d9-78d7f109aafe
-- title:
--   Weight Two: exists sec finsum
-- statement:
--   The Weight Two construction uses the exists sec finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecFinsum.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecFinsum.lean#L22-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecFinsum
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
open GlobalTheory GlobalTheory.WeightTwo

theorem GlobalTheory.WeightTwo.exists_sec_finsum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {I : Type} (s : Finset I) (d : I → LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval t r z J = ∑ i ∈ s, sval (d i) r z J := by sorry
