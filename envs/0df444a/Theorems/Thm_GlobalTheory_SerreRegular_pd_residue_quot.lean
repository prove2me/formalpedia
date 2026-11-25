-- Prove2me | Theorems.Thm_GlobalTheory_SerreRegular_pd_residue_quot
-- name    : GlobalTheory.SerreRegular.pd_residue_quot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:30.435164+00:00
-- url     : https://prove2.me/theorems/eee128b2-cf49-4122-ba6e-ba2162eb2d28
-- title:
--   Serre Regular: pd residue quot
-- statement:
--   The Serre Regular construction uses the pd residue quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L166-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L166-L215

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
open GlobalTheory.SerreRegular

theorem GlobalTheory.SerreRegular.pd_residue_quot {A : Type} [CommRing A] [IsLocalRing A] {x : A}
    (hm : x ∈ maximalIdeal A) (hm2 : x ∉ maximalIdeal A ^ 2) [IsLocalRing (A ⧸ Ideal.span {x})]
    (n : ℕ) (h : HasProjectiveDimensionLE
      (ModuleCat.of (A ⧸ Ideal.span {x}) ((A ⧸ Ideal.span {x}) ⊗[A] maximalIdeal A)) n) :
    HasProjectiveDimensionLE (ModuleCat.of (A ⧸ Ideal.span {x})
      ((A ⧸ Ideal.span {x}) ⧸ maximalIdeal (A ⧸ Ideal.span {x}))) n := by sorry
