-- Prove2me | Theorems.Thm_GlobalTheory_abs_entry_le_of_psd_le
-- name    : GlobalTheory.abs_entry_le_of_psd_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:04:51.546916+00:00
-- url     : https://prove2.me/theorems/1af67405-bd36-48fa-b308-85e8040cd404
-- title:
--   Global Theory: abs entry le of psd le
-- statement:
--   The Global Theory construction uses the abs entry le of psd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormDetOfRealLeFactorialMulPow.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormDetOfRealLeFactorialMulPow.lean#L15-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormDetOfRealLeFactorialMulPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.abs_entry_le_of_psd_le (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ)
    (hY : Y.PosSemidef) (hMY : (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) (i j : Fin g) :
    |Y i j| ≤ M := by sorry
