-- Prove2me | Theorems.Thm_GlobalTheory_Exist_ProdOpen_bijective_baseChange
-- name    : GlobalTheory.Exist.ProdOpen.bijective_baseChange
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:07:17.411782+00:00
-- url     : https://prove2.me/theorems/b9f7bf6f-170c-4820-a254-2a554cf8491a
-- title:
--   Prod Open: bijective base Change
-- statement:
--   The Prod Open construction uses the bijective base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LineBundleTrivialBasicOpenOfTrivialFibreProduct.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LineBundleTrivialBasicOpenOfTrivialFibreProduct.lean#L50-L56

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

theorem GlobalTheory.Exist.ProdOpen.bijective_baseChange {R T : Type} [CommRing R] [CommRing T] (g₁ : R →+* T) (X : Over (Sp R))
    (h : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom)) :
    (∀ (R' : Type) [CommRing R'] (g : T →+* R') (X' : Scheme.{0}) (π : X' ⟶ ((Over.pullback (Spec.map (CommRingCat.ofHom g₁))).obj X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' ((Over.pullback (Spec.map (CommRingCat.ofHom g₁))).obj X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) := by sorry
