-- Prove2me | Theorems.Thm_GlobalTheory_HCA_dw_le_sup
-- name    : GlobalTheory.HCA.dw_le_sup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:59:48.917597+00:00
-- url     : https://prove2.me/theorems/34b91d3c-fc01-45e4-81fc-0c426a766bc1
-- title:
--   HCA: dw le sup
-- statement:
--   The HCA construction uses the dw le sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticWeakSolWordDerivLeConstMulSup.lean#L41-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticWeakSolWordDerivLeConstMulSup.lean#L41-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory.HCA.SupEst

theorem GlobalTheory.HCA.dw_le_sup : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ (w : List (Fin d)), ∀ x₀ ∈ U, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u U → WeakSol P U u → ∀ M : ℝ, (∀ x ∈ U, ‖u x‖ ≤ M) → ‖dw w u x₀‖ ≤ C * M := by sorry
