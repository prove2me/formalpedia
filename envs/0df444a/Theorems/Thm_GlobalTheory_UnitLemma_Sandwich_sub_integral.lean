-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_sub_integral
-- name    : GlobalTheory.UnitLemma.Sandwich.sub_integral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:29:47.344233+00:00
-- url     : https://prove2.me/theorems/6176e91c-158a-42db-a6ef-9979494a9da8
-- title:
--   Sandwich: sub integral
-- statement:
--   The Sandwich construction uses the sub integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FullLatticeSandwichBetweenIntegralElements.lean#L108-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FullLatticeSandwichBetweenIntegralElements.lean#L108-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Sandwich
variable {K : UQ} (B : InvAlg K)

theorem GlobalTheory.UnitLemma.Sandwich.sub_integral (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O) (L : Submodule K.O B.A) (hL : L.FG) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by sorry
