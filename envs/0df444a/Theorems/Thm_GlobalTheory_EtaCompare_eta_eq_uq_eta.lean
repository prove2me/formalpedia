-- Prove2me | Theorems.Thm_GlobalTheory_EtaCompare_eta_eq_uq_eta
-- name    : GlobalTheory.EtaCompare.eta_eq_uq_eta
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:42.648012+00:00
-- url     : https://prove2.me/theorems/7238cf8e-c351-4c78-9129-19db3506987c
-- title:
--   Eta Compare: eta eq uq eta
-- statement:
--   The Eta Compare construction uses the eta eq uq eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormLeIffValuationLe.lean#L49-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormLeIffValuationLe.lean#L49-L95

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

theorem GlobalTheory.EtaCompare.eta_eq_uq_eta : ∀ (K : UQ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (φ : K.E ≃+* E),
    (∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) →
    ∀ x : F, GlobalTheory.JR.eta x = ((K.eta (φ.symm (algebraMap F E x)) : ℚ) : ℂ) := by sorry
