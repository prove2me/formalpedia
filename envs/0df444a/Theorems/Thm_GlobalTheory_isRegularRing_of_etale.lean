-- Prove2me | Theorems.Thm_GlobalTheory_isRegularRing_of_etale
-- name    : GlobalTheory.isRegularRing_of_etale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:30.103702+00:00
-- url     : https://prove2.me/theorems/d3b782ed-651c-46c7-98d4-4d5e07fced49
-- title:
--   Global Theory: is Regular Ring of etale
-- statement:
--   The Global Theory construction uses the is Regular Ring of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfSmooth.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfSmooth.lean#L42-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
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

theorem GlobalTheory.isRegularRing_of_etale (R S : Type*) [CommRing R] [IsRegularRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : IsRegularRing S := by sorry
