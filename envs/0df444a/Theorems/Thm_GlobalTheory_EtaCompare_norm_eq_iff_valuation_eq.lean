-- Prove2me | Theorems.Thm_GlobalTheory_EtaCompare_norm_eq_iff_valuation_eq
-- name    : GlobalTheory.EtaCompare.norm_eq_iff_valuation_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:59.298128+00:00
-- url     : https://prove2.me/theorems/abdee475-59d8-4d8d-be57-8d8cd82ba828
-- title:
--   Eta Compare: norm eq iff valuation eq
-- statement:
--   The Eta Compare construction uses the norm eq iff valuation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormLeIffValuationLe.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormLeIffValuationLe.lean#L27-L41

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormLeIffValuationLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.EtaCompare
open WithZero

theorem GlobalTheory.EtaCompare.norm_eq_iff_valuation_eq (K : UQ) {E : Type} [NormedField E] (φ : K.E ≃+* E)
    (hball : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (a b : K.E) :
    ‖φ a‖ = ‖φ b‖ ↔ (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b := by sorry
