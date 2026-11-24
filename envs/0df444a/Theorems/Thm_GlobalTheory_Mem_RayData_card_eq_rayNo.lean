-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_card_eq_rayNo
-- name    : GlobalTheory.Mem.RayData.card_eq_rayNo
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:24:58.287542+00:00
-- url     : https://prove2.me/theorems/ad7f1029-a83c-4ad5-8cdb-a1bf443fdfe2
-- title:
--   Ray Data: card eq ray No
-- statement:
--   The Ray Data construction uses the card eq ray No property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean#L158-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean#L158-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIntegralOfMemRayI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayData
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem GlobalTheory.Mem.RayData.card_eq_rayNo : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), M ≠ 0 →
    ∀ D : _root_.GlobalTheory.Mem.RayData K M,
    Fintype.card D.G =
      _root_.GlobalTheory.Mem.An.rayNo (Ideal.span {(M : NumberField.RingOfIntegers K)}) := by sorry
