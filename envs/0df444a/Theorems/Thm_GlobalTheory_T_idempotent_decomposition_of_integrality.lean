-- Prove2me | Theorems.Thm_GlobalTheory_T_idempotent_decomposition_of_integrality
-- name    : GlobalTheory.T.idempotent_decomposition_of_integrality
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:33.873421+00:00
-- url     : https://prove2.me/theorems/3cbde352-631e-4c39-930c-374bc91702cf
-- title:
--   T: idempotent decomposition of integrality
-- statement:
--   The T construction uses the idempotent decomposition of integrality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdempotentDecompositionOfIntegralityStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdempotentDecompositionOfIntegralityStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegrality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegralityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.idempotent_decomposition_of_integrality : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] [IsUltrametricDist F] (A : Et F E), (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) → ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧ (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧ ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by sorry
