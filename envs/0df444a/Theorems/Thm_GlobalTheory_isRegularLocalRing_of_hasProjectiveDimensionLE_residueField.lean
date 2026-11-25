-- Prove2me | Theorems.Thm_GlobalTheory_isRegularLocalRing_of_hasProjectiveDimensionLE_residueField
-- name    : GlobalTheory.isRegularLocalRing_of_hasProjectiveDimensionLE_residueField
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:02.357954+00:00
-- url     : https://prove2.me/theorems/d79b451b-4f1f-4f08-84fa-872fd58f0f90
-- title:
--   Global Theory: is Regular Local Ring of has Projective Dimension LE residue Field
-- statement:
--   The Global Theory construction uses the is Regular Local Ring of has Projective Dimension LE residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L290-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L290-L294

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

theorem GlobalTheory.isRegularLocalRing_of_hasProjectiveDimensionLE_residueField (A : Type) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ maximalIdeal A)) n) :
    IsRegularLocalRing A := by sorry
