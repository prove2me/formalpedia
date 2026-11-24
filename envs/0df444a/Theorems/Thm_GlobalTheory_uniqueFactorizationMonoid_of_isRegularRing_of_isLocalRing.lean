-- Prove2me | Theorems.Thm_GlobalTheory_uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
-- name    : GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:24.660899+00:00
-- url     : https://prove2.me/theorems/2ae947ae-40be-4bc8-80c8-4740dac10f1f
-- title:
--   Global Theory: unique Factorization Monoid of is Regular Ring of is Local Ring
-- statement:
--   The Global Theory construction uses the unique Factorization Monoid of is Regular Ring of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/UniqueFactorizationMonoidOfIsRegularRingOfIsLoca.lean#L196-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/UniqueFactorizationMonoidOfIsRegularRingOfIsLoca.lean#L196-L211

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open IsLocalRing

theorem GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing :
    (∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R)
      (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R I) n →
      Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal) →
    ∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R],
      UniqueFactorizationMonoid R := by sorry
