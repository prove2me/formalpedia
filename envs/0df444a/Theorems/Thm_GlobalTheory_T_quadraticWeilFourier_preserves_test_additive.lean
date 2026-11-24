-- Prove2me | Theorems.Thm_GlobalTheory_T_quadraticWeilFourier_preserves_test_additive
-- name    : GlobalTheory.T.quadraticWeilFourier_preserves_test_additive
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:55:27.961069+00:00
-- url     : https://prove2.me/theorems/ba95e4f7-c684-46fe-b886-7c7d47d258f4
-- title:
--   T: quadratic Weil Fourier preserves test additive
-- statement:
--   The T construction uses the quadratic Weil Fourier preserves test additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierPreservesTestAdditiveStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierPreservesTestAdditiveStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quadraticWeilFourier_preserves_test_additive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → IsTest (fOp A ψ x μ φ) ∧ ∀ φ' : A.L → ℂ, IsTest φ' → fOp A ψ x μ (φ + φ') = fOp A ψ x μ φ + fOp A ψ x μ φ' := by sorry
