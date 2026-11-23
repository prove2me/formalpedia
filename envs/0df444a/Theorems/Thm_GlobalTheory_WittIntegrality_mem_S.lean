-- Prove2me | Theorems.Thm_GlobalTheory_WittIntegrality_mem_S
-- name    : GlobalTheory.WittIntegrality.mem_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:02.781821+00:00
-- url     : https://prove2.me/theorems/56a6bf9a-a3ea-4208-8c1e-e6304e5f8ef9
-- title:
--   Witt Integrality: mem S
-- statement:
--   The Witt Integrality construction uses the mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean#L29-L38

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
open GlobalTheory.WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}

theorem GlobalTheory.WittIntegrality.mem_S (x : WittVector p C) : x ∈ S A p ↔ ∀ k, x.coeff k ∈ A := by sorry
