-- Prove2me | Theorems.Thm_GlobalTheory_surjective_of_generic_fibre_subset_range
-- name    : GlobalTheory.surjective_of_generic_fibre_subset_range
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:10.696121+00:00
-- url     : https://prove2.me/theorems/14c8f42c-906b-44b6-b099-b900418abb4a
-- title:
--   Global Theory: surjective of generic fibre subset range
-- statement:
--   The Global Theory construction uses the surjective of generic fibre subset range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeOfGenericallySurjective.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeOfGenericallySurjective.lean#L9-L24

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

theorem GlobalTheory.surjective_of_generic_fibre_subset_range
    {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp V) [UniversallyClosed f] [Flat g]
    (h : ∀ y : Y, g y ∈ Set.range (spMap (algebraMap V K)) → y ∈ Set.range f) :
    Surjective f := by sorry
