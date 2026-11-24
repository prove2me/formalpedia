-- Prove2me | Theorems.Thm_GlobalTheory_T_additiveSystem_preparation_normalForm_one
-- name    : GlobalTheory.T.additiveSystem_preparation_normalForm_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:36.273734+00:00
-- url     : https://prove2.me/theorems/14aba24c-fa72-4c64-8a7e-3861c176f8fa
-- title:
--   T: additive System preparation normal Form one
-- statement:
--   The T construction uses the additive System preparation normal Form one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.additiveSystem_preparation_normalForm_one : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → 1 ≤ D → ∀ M : ℕ → Matrix m m F, Normal 1 M → ∃ (A : Matrix m m F) (U : ℕ → Matrix m m F), (∀ i j, ‖A i j‖ ≤ 1) ∧ (∀ i j, ‖(U 0 - 1) i j‖ < 1) ∧ (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) ∧ M 0 = -(U 0 * A) ∧ ∀ x : m → F, gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by sorry
