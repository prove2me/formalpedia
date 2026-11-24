-- Prove2me | Theorems.Thm_GlobalTheory_ExtendRig_isLocalization_away_of_irreducible
-- name    : GlobalTheory.ExtendRig.isLocalization_away_of_irreducible
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:18:10.603007+00:00
-- url     : https://prove2.me/theorems/c42c348c-25f5-4861-b8ce-b86496136a0f
-- title:
--   Extend Rig: is Localization away of irreducible
-- statement:
--   The Extend Rig construction uses the is Localization away of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfIsDiscreteValuationRing.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfIsDiscreteValuationRing.lean#L29-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfIsDiscreteValuationRing
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
open GlobalTheory GlobalTheory.ExtendRig

theorem GlobalTheory.ExtendRig.isLocalization_away_of_irreducible (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by sorry
