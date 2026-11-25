-- Prove2me | Theorems.Thm_GlobalTheory_T_continuousOn_norm_diag_of_triangular_factor
-- name    : GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:45.150068+00:00
-- url     : https://prove2.me/theorems/213caa64-bf82-411a-8f7a-cd5f6411fcb1
-- title:
--   T: continuous On norm diag of triangular factor
-- statement:
--   The T construction uses the continuous On norm diag of triangular factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContinuousOnNormDiagOfTriangularSqrtStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContinuousOnNormDiagOfTriangularSqrtStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by sorry
