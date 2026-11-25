-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_descendedFunction_eq_partialFourier
-- name    : GlobalTheory.T.fourier_descendedFunction_eq_partialFourier
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:07.192943+00:00
-- url     : https://prove2.me/theorems/502eeb4b-9ba3-56ce-aa03-a84cc1c0e4dc
-- title:
--   T: fourier descended Function eq partial Fourier
-- statement:
--   The T construction uses the fourier descended Function eq partial Fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierDescendedFunctionEqPartialFourierStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierDescendedFunctionEqPartialFourierStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierDescendedFunctionEqPartialFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierDescendedFunctionEqPartialFourierStatement
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

theorem GlobalTheory.T.fourier_descendedFunction_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by sorry
