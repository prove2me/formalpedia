-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_unique_min_and_sums_separated
-- name    : GlobalTheory.exists_basis_unique_min_and_sums_separated
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:49.620033+00:00
-- url     : https://prove2.me/theorems/f19f7a19-23fa-463f-8bd0-ac8b866adbec
-- title:
--   Global Theory: exists basis unique min and sums separated
-- statement:
--   The Global Theory construction uses the exists basis unique min and sums separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisUniqueMinAndSumsSeparated.lean#L40-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisUniqueMinAndSumsSeparated.lean#L40-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinAndSumsSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.exists_basis_unique_min_and_sums_separated :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → ∀ (d g N N' D : ℕ), finrank ℤ X = d → d ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → 2 * (D : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) * N < N' → ∃ e : Basis (Fin d) ℤ X, (∀ (i : Fin d) (μ : X), μ ≠ 0 → q (e i) < q (e i + N • μ) ∧ q (-e i) < q (-e i + N • μ)) ∧ ∀ (k : ℕ) (α β : Fin k → X), k ≤ D → (∀ j w, q (α j) ≤ q (α j + N • w)) → (∀ j w, q (β j) ≤ q (β j + N • w)) → ∀ w : X, ∑ j, α j = ∑ j, β j + N' • w → w = 0 := by sorry
