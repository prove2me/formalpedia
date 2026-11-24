-- Prove2me | Theorems.Thm_GlobalTheory_T_unramifiedValuationParitySign_character_kernel_norms
-- name    : GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:02.759707+00:00
-- url     : https://prove2.me/theorems/6b3e0b9b-bcb6-4d02-9288-b4a5e1824226
-- title:
--   T: unramified Valuation Parity Sign character kernel norms
-- statement:
--   The T construction uses the unramified Valuation Parity Sign character kernel norms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedValuationParitySignCharacterKernelNormStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedValuationParitySignCharacterKernelNormStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
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

theorem GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by sorry
