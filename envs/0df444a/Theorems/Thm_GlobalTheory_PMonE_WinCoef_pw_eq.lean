-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_WinCoef_pw_eq
-- name    : GlobalTheory.PMonE.WinCoef.pw_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:59.529565+00:00
-- url     : https://prove2.me/theorems/5f2ed66d-ceb5-49ed-8901-7d567cf0d587
-- title:
--   Win Coef: pw eq
-- statement:
--   The Win Coef construction uses the pw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowSummedRowPowEqAdditiveSystemPowerSum.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowSummedRowPowEqAdditiveSystemPowerSum.lean#L27-L36

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

theorem GlobalTheory.PMonE.WinCoef.pw_eq (k : ℤ) (x : F) : pw p k x = ((frobAut (F := F) p) ^ k) x := by sorry
