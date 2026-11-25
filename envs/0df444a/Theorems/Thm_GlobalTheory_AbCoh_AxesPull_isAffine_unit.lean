-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_AxesPull_isAffine_unit
-- name    : GlobalTheory.AbCoh.AxesPull.isAffine_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:20:43.591895+00:00
-- url     : https://prove2.me/theorems/254d5c1a-bdd4-4e23-884c-c8cc0e23a04e
-- title:
--   Axes Pull: is Affine unit
-- statement:
--   The Axes Pull construction uses the is Affine unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GrpObjPullbackAxesCohomologyProjections.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GrpObjPullbackAxesCohomologyProjections.lean#L15-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GrpObjPullbackAxesCohomologyProjections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.AxesPull
variable {R : Type} [CommRing R]

theorem GlobalTheory.AbCoh.AxesPull.isAffine_unit : IsAffine (𝟙_ (Over (Sp R))).left := by sorry
