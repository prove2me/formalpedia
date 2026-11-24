-- Prove2me | Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_real_cexp
-- name    : GlobalTheory.norm_iteratedFDeriv_real_cexp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:56.022008+00:00
-- url     : https://prove2.me/theorems/5ff05338-f389-46ee-a6e9-62e921a3daa2
-- title:
--   Global Theory: norm iterated FDeriv real cexp
-- statement:
--   The Global Theory construction uses the norm iterated FDeriv real cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivCexpPhaseLe.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivCexpPhaseLe.lean#L10-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivCexpPhaseLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open scoped Nat
noncomputable section
open GlobalTheory

theorem GlobalTheory.norm_iteratedFDeriv_real_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by sorry
