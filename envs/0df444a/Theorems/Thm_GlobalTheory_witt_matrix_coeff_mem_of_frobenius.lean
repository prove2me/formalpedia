-- Prove2me | Theorems.Thm_GlobalTheory_witt_matrix_coeff_mem_of_frobenius
-- name    : GlobalTheory.witt_matrix_coeff_mem_of_frobenius
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:30.514803+00:00
-- url     : https://prove2.me/theorems/e7377932-60e7-43e0-8054-e492c78cf150
-- title:
--   Global Theory: witt matrix coeff mem of frobenius
-- statement:
--   The Global Theory construction uses the witt matrix coeff mem of frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean#L174-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean#L174-L189

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open WittIntegrality

theorem GlobalTheory.witt_matrix_coeff_mem_of_frobenius : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [CharP C p] [PerfectRing C p] (A : ValuationSubring C) {n : Type} [Fintype n] (Z : Matrix n n (WittVector p C)) (Y : Matrix n n (WittVector p A)), (Z.map WittVector.frobenius = Y.map (WittVector.map A.subtype) * Z ∨ Z.map WittVector.frobenius = Z * Y.map (WittVector.map A.subtype)) → ∀ i j m, (Z i j).coeff m ∈ A := by sorry
