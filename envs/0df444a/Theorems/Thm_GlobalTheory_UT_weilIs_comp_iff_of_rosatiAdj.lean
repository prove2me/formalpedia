-- Prove2me | Theorems.Thm_GlobalTheory_UT_weilIs_comp_iff_of_rosatiAdj
-- name    : GlobalTheory.UT.weilIs_comp_iff_of_rosatiAdj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:25.565289+00:00
-- url     : https://prove2.me/theorems/1758d073-5960-5976-a41c-9dca46ac6188
-- title:
--   UT: weil Is comp iff of rosati Adj
-- statement:
--   The UT construction uses the weil Is comp iff of rosati Adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/WeilIsCompIffOfRosatiAdj.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/WeilIsCompIffOfRosatiAdj.lean#L21-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_WeilIsCompIffOfRosatiAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
open GlobalTheory GlobalTheory.UT

theorem GlobalTheory.UT.weilIs_comp_iff_of_rosatiAdj : LL → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → RosatiAdj P.A P.L a a' → ∀ (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P.A P.L k (x ≫ a) y c ↔ WeilIs P.A P.L k x (y ≫ a') c := by sorry
