-- Prove2me | Theorems.Thm_GlobalTheory_RegularFactorial_isRegularRing_of_isLocalization
-- name    : GlobalTheory.RegularFactorial.isRegularRing_of_isLocalization
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:37.224477+00:00
-- url     : https://prove2.me/theorems/b304cd2b-c0db-5e21-86fe-76c016c7a716
-- title:
--   Regular Factorial: is Regular Ring of is Localization
-- statement:
--   The Regular Factorial construction uses the is Regular Ring of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/UniqueFactorizationMonoidOfIsRegularRingOfIsLoca.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/UniqueFactorizationMonoidOfIsRegularRingOfIsLoca.lean#L15-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.RegularFactorial
open IsLocalRing

theorem GlobalTheory.RegularFactorial.isRegularRing_of_isLocalization {R : Type*} [CommRing R] [IsRegularRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsRegularRing S := by sorry
