-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_localization_augmentation
-- name    : GlobalTheory.exists_algHom_localization_augmentation
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:05.725801+00:00
-- url     : https://prove2.me/theorems/c334cdea-220f-5ba7-8686-689ec93d57a3
-- title:
--   Global Theory: exists alg Hom localization augmentation
-- statement:
--   The Global Theory construction uses the exists alg Hom localization augmentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAlgHomLocalizationAugmentation.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAlgHomLocalizationAugmentation.lean#L18-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTorsionPointFrobeniusLocalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionLocalPresentationSmoothGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAlgHomLocalizationAugmentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_algHom_localization_augmentation (O : Type) [CommRing O] [IsLocalRing O]
    (H : Type) [CommRing H] [Algebra O H] (ε : H →ₐ[O] O) :
    ∃ εT : Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε) →ₐ[O] O,
      ∀ h, εT (algebraMap H _ h) = ε h := by sorry
