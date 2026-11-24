-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_Idem_main
-- name    : GlobalTheory.JR.Et.Idem.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:33:24.329835+00:00
-- url     : https://prove2.me/theorems/15d32fb6-6873-4f84-909b-2bb52964a4e7
-- title:
--   Idem: main
-- statement:
--   The Idem construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdempotentDecompositionOfIntegrality.lean#L47-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdempotentDecompositionOfIntegrality.lean#L47-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegrality
import Theorems.Thm_GlobalTheory_IntegralPi_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et GlobalTheory.JR.Et.Idem

theorem GlobalTheory.JR.Et.Idem.main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] [IsUltrametricDist F] (A : Et F E),
    (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
      IsIntegral (NormedField.valuation (K := F)).integer y ∨
        IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) →
    ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧
      (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧
      ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by sorry
