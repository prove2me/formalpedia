-- Prove2me | Theorems.Thm_GlobalTheory_SerreRegular_regular_of_quotient
-- name    : GlobalTheory.SerreRegular.regular_of_quotient
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:45.099798+00:00
-- url     : https://prove2.me/theorems/038b760c-8e2d-4787-90fc-a06958acdf7c
-- title:
--   Serre Regular: regular of quotient
-- statement:
--   The Serre Regular construction uses the regular of quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L136-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L136-L164

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

theorem GlobalTheory.SerreRegular.regular_of_quotient {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : IsSMulRegular A x) (hm : x ∈ maximalIdeal A)
    [IsRegularLocalRing (A ⧸ Ideal.span {x})] : IsRegularLocalRing A := by sorry
