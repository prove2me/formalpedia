-- Prove2me | Theorems.Thm_GlobalTheory_isRegularLocalRing_of_flat_of_map_eq_maximalIdeal
-- name    : GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:57.141251+00:00
-- url     : https://prove2.me/theorems/50f2e23a-bddd-48f0-8fe1-d7301944694c
-- title:
--   Global Theory: is Regular Local Ring of flat of map eq maximal Ideal
-- statement:
--   The Global Theory construction uses the is Regular Local Ring of flat of map eq maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L296-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L296-L305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory

theorem GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal (R S : Type) [CommRing R]
    [IsRegularLocalRing R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [Module.Flat R S] (q : Ideal R) (hq : maximalIdeal S = q.map (algebraMap R S)) :
    IsRegularLocalRing S := by sorry
