-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_WinCoef_pw_win
-- name    : GlobalTheory.PMonE.WinCoef.pw_win
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:43.578079+00:00
-- url     : https://prove2.me/theorems/ac9f34fe-a79c-46aa-8ea4-2e6539f7d95b
-- title:
--   Win Coef: pw win
-- statement:
--   The Win Coef construction uses the pw win property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowSummedRowPowEqAdditiveSystemPowerSum.lean#L41-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowSummedRowPowEqAdditiveSystemPowerSum.lean#L41-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open Finset
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.WinCoef
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem GlobalTheory.PMonE.WinCoef.pw_win (h r L : ℕ) (hr : r ≤ h) (hL : 1 ≤ L) (n : ℤ) (hn : -(L : ℤ) ≤ n) (z : F) :
    pw p ((r : ℤ) + n * h) (z ^ (p ^ h) ^ (L - 1)) ^ p ^ (h - r) = z ^ (p ^ h) ^ ((n + L).toNat) := by sorry
