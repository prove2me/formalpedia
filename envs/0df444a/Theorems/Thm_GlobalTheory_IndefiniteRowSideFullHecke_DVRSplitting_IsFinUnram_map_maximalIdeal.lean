-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DVRSplitting_IsFinUnram_map_maximalIdeal
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting.IsFinUnram.map_maximalIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:34.316527+00:00
-- url     : https://prove2.me/theorems/efc492e5-d345-4e44-9cd0-30607a7b50e3
-- title:
--   Is Fin Unram: map maximal Ideal
-- statement:
--   The Is Fin Unram construction uses the map maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/DVRSplitting.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/DVRSplitting.lean#L17-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_DVRSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting.IsFinUnram.map_maximalIdeal {V W : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W] (h : IsFinUnram V W) :
    IsLocalHom (algebraMap V W) ∧ (maximalIdeal V).map (algebraMap V W) = maximalIdeal W := by sorry
