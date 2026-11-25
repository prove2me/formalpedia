-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_isClosedImmersion_of_isPullback_surj
-- name    : GlobalTheory.AbCoh.isClosedImmersion_of_isPullback_surj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:20:35.756624+00:00
-- url     : https://prove2.me/theorems/bd248fdb-06d7-4185-8b65-f017769c9da3
-- title:
--   Ab Coh: is Closed Immersion of is Pullback surj
-- statement:
--   The Ab Coh construction uses the is Closed Immersion of is Pullback surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFibreClassEqZeroOfSmulPullbackEqZero.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFibreClassEqZeroOfSmulPullbackEqZero.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairFstPreimageRestrictionBijectiveClosedImmersiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyClassPullbackReductionPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFibreClassEqZeroOfSmulPullbackEqZero
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
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.isClosedImmersion_of_isPullback_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {q' : Y' ⟶ Sp R'} {χ : Y' ⟶ Y}
    (k : IsPullback χ q' q (spMap σ)) : IsClosedImmersion χ := by sorry
