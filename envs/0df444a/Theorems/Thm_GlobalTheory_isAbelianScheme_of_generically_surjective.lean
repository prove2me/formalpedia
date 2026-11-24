-- Prove2me | Theorems.Thm_GlobalTheory_isAbelianScheme_of_generically_surjective
-- name    : GlobalTheory.isAbelianScheme_of_generically_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:27.572216+00:00
-- url     : https://prove2.me/theorems/7631b547-4613-4fc2-bfef-9b8dddf0a44a
-- title:
--   Global Theory: is Abelian Scheme of generically surjective
-- statement:
--   The Global Theory construction uses the is Abelian Scheme of generically surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeOfGenericallySurjective.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeOfGenericallySurjective.lean#L26-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeOfGenericallySurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.isAbelianScheme_of_generically_surjective :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (B G : Over (Sp V)) [GrpObj B] [GrpObj G],
      IsAbelianScheme B → IsSemiAbelian G → ∀ ψ : B ⟶ G,
      (∀ x : G.left, G.hom x ∈ Set.range (spMap (algebraMap V K)) → x ∈ Set.range ψ.left) →
      IsAbelianScheme G := by sorry
