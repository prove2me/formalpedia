-- Prove2me | Theorems.Thm_GlobalTheory_IntConj_exists_commuting_mul_integral
-- name    : GlobalTheory.IntConj.exists_commuting_mul_integral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:51:30.177975+00:00
-- url     : https://prove2.me/theorems/96b77125-afb3-464b-a0e3-7fa1c4d3e7af
-- title:
--   Int Conj: exists commuting mul integral
-- statement:
--   The Int Conj construction uses the exists commuting mul integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommutantMulIntegralConjugate.lean#L50-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommutantMulIntegralConjugate.lean#L50-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorOfSeparableCharpolyField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorSemilocalOfCyclicVectorField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommutantMulIntegralConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IntConj

theorem GlobalTheory.IntConj.exists_commuting_mul_integral (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N x : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hsep : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (hx : IsUnit x) (hN' : ∀ i j, ‖(x⁻¹ * N * x) i j‖ ≤ 1) :
    ∃ c : Matrix (Fin n) (Fin n) E, IsUnit c ∧ c * N = N * c ∧ (∀ i j, ‖(c⁻¹ * x) i j‖ ≤ 1) ∧
      ‖(c⁻¹ * x).det‖ = 1 := by sorry
