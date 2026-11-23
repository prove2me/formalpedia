-- Prove2me | Theorems.Thm_GlobalTheory_EtaChar_eta_eq_neg_one_iff
-- name    : GlobalTheory.EtaChar.eta_eq_neg_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:21.798891+00:00
-- url     : https://prove2.me/theorems/e3405273-6003-46e9-9e35-e2ce949e2fc1
-- title:
--   Eta Char: eta eq neg one iff
-- statement:
--   The Eta Char construction uses the eta eq neg one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedValuationParitySignCharacterKernelNorm.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedValuationParitySignCharacterKernelNorm.lean#L48-L53

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

theorem GlobalTheory.EtaChar.eta_eq_neg_one_iff {F : Type} [NormedField F] (x : F) : eta x = -1 ↔ ¬ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by sorry
