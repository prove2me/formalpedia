-- Prove2me | Theorems.Thm_GlobalTheory_SerreRegular_pd_quot
-- name    : GlobalTheory.SerreRegular.pd_quot
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:26.478466+00:00
-- url     : https://prove2.me/theorems/f1d7928a-68c3-4117-b53f-cc413597a5cc
-- title:
--   Serre Regular: pd quot
-- statement:
--   The Serre Regular construction uses the pd quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L51-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L51-L78

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

theorem GlobalTheory.SerreRegular.pd_quot {A : Type} [CommRing A] [IsNoetherianRing A] {x : A} (hx : IsSMulRegular A x)
    (n : ℕ) (M : ModuleCat.{0} A) [Module.Finite A M] (hM : IsSMulRegular M x)
    (h : HasProjectiveDimensionLE M n) :
    HasProjectiveDimensionLE (ModuleCat.of (A ⧸ Ideal.span {x}) ((A ⧸ Ideal.span {x}) ⊗[A] M)) n := by sorry
