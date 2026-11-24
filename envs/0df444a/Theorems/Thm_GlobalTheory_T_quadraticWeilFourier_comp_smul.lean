-- Prove2me | Theorems.Thm_GlobalTheory_T_quadraticWeilFourier_comp_smul
-- name    : GlobalTheory.T.quadraticWeilFourier_comp_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:55:41.953699+00:00
-- url     : https://prove2.me/theorems/6d405364-8807-4c02-91bb-7156c3e7a944
-- title:
--   T: quadratic Weil Fourier comp smul
-- statement:
--   The T construction uses the quadratic Weil Fourier comp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierCompSmulStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierCompSmulStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierCompSmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierCompSmulStatement
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

theorem GlobalTheory.T.quadraticWeilFourier_comp_smul : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y, fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y = ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by sorry
