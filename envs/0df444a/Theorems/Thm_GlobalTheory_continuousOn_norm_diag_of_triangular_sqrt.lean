-- Prove2me | Theorems.Thm_GlobalTheory_continuousOn_norm_diag_of_triangular_sqrt
-- name    : GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:50.01688+00:00
-- url     : https://prove2.me/theorems/159ef9d5-0d8d-4983-b340-6c127223bd1a
-- title:
--   Global Theory: continuous On norm diag of triangular sqrt
-- statement:
--   The Global Theory construction uses the continuous On norm diag of triangular sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContinuousOnNormDiagOfTriangularSqrt.lean#L63-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContinuousOnNormDiagOfTriangularSqrt.lean#L63-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix

theorem GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by sorry
