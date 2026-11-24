-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_normal_of_inv_mul
-- name    : GlobalTheory.PMonE.normal_of_inv_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:28.522424+00:00
-- url     : https://prove2.me/theorems/46018131-caf2-4a62-9ad4-d2a3317e030d
-- title:
--   PMon E: normal of inv mul
-- statement:
--   The PMon E construction uses the normal of inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMul.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMul.lean#L61-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE
open Finset

theorem GlobalTheory.PMonE.normal_of_inv_mul : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m]
    [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) →
    (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 →
    Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by sorry
