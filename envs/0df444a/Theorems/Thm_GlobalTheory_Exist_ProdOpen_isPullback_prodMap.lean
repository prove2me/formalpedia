-- Prove2me | Theorems.Thm_GlobalTheory_Exist_ProdOpen_isPullback_prodMap
-- name    : GlobalTheory.Exist.ProdOpen.isPullback_prodMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:43.812393+00:00
-- url     : https://prove2.me/theorems/85767caf-ecc9-47f3-bbe9-e8fa8e47f7f5
-- title:
--   Prod Open: is Pullback prod Map
-- statement:
--   The Prod Open construction uses the is Pullback prod Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LineBundleTrivialBasicOpenOfTrivialFibreProduct.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LineBundleTrivialBasicOpenOfTrivialFibreProduct.lean#L27-L35

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

theorem GlobalTheory.Exist.ProdOpen.isPullback_prodMap :
    IsPullback (prodMap φ X Y) ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
      (X ⊗ Y).hom φ := by sorry
