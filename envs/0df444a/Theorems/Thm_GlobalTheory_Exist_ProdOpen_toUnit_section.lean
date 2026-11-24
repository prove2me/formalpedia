-- Prove2me | Theorems.Thm_GlobalTheory_Exist_ProdOpen_toUnit_section
-- name    : GlobalTheory.Exist.ProdOpen.toUnit_section
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:07:44.694157+00:00
-- url     : https://prove2.me/theorems/2bc2bf9c-ded1-4552-bb1f-930cfccfb2f9
-- title:
--   Prod Open: to Unit section
-- statement:
--   The Prod Open construction uses the to Unit section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LineBundleTrivialBasicOpenOfTrivialFibreProduct.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LineBundleTrivialBasicOpenOfTrivialFibreProduct.lean#L43-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TrivProdOfSmallExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LineBundleTrivialBasicOpenOfTrivialFibreProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.ProdOpen
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (X Y : Over S)

theorem GlobalTheory.Exist.ProdOpen.toUnit_section (y : 𝟙_ (Over S) ⟶ Y) :
    toUnit ((Over.pullback φ).obj X) ≫ Functor.LaxMonoidal.ε (Over.pullback φ) ≫
      (Over.pullback φ).map y = (Over.pullback φ).map (toUnit X ≫ y) := by sorry
