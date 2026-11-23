-- Prove2me | Theorems.Thm_GlobalTheory_WittIntegrality_key
-- name    : GlobalTheory.WittIntegrality.key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:35.263867+00:00
-- url     : https://prove2.me/theorems/476a618a-4fc9-4169-b631-31e282a7a783
-- title:
--   Witt Integrality: key
-- statement:
--   The Witt Integrality construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean#L129-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean#L129-L169

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
variable [CharP C p]
variable [PerfectRing C p]

theorem GlobalTheory.WittIntegrality.key {n : Type} [Fintype n] (Y : Matrix n n (WittVector p C)) (hY : ∀ i j, Y i j ∈ S A p) :
    ∀ (k : ℕ) (Z B : Matrix n n (WittVector p C)), (∀ i j, B i j ∈ S A p) →
    (∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) →
    ∀ i j, (Z i j).coeff k ∈ A := by sorry
