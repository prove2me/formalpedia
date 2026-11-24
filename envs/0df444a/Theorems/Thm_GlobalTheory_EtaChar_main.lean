-- Prove2me | Theorems.Thm_GlobalTheory_EtaChar_main
-- name    : GlobalTheory.EtaChar.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:32.480462+00:00
-- url     : https://prove2.me/theorems/464c72d4-bc21-449b-8cac-2437f6cfdd61
-- title:
--   Eta Char: main
-- statement:
--   The Eta Char construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedValuationParitySignCharacterKernelNorm.lean#L98-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedValuationParitySignCharacterKernelNorm.lean#L98-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.EtaChar

theorem GlobalTheory.EtaChar.main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by sorry
