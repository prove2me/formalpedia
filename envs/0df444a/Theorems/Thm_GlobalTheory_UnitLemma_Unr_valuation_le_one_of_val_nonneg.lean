-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_valuation_le_one_of_val_nonneg
-- name    : GlobalTheory.UnitLemma.Unr.valuation_le_one_of_val_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:22.181634+00:00
-- url     : https://prove2.me/theorems/b5e0d5a7-b711-45a1-b6ab-e9d5fdfac435
-- title:
--   Unr: valuation le one of val nonneg
-- statement:
--   The Unr construction uses the valuation le one of val nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedInvolutionExtMapsIntegersToIntegers.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedInvolutionExtMapsIntegersToIntegers.lean#L10-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedInvolutionExtMapsIntegersToIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.Unr.valuation_le_one_of_val_nonneg (K : UQ) (e : K.E) (he : e ≠ 0) (h : 0 ≤ val K.O e) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≤ 1 := by sorry
