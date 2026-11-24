-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_WinCoef_frob_inv_pow_apply
-- name    : GlobalTheory.PMonE.WinCoef.frob_inv_pow_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:51.442235+00:00
-- url     : https://prove2.me/theorems/fe3f9728-d00c-43f2-80b4-85af2d8ade10
-- title:
--   Win Coef: frob inv pow apply
-- statement:
--   The Win Coef construction uses the frob inv pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowSummedRowPowEqAdditiveSystemPowerSum.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowSummedRowPowEqAdditiveSystemPowerSum.lean#L20-L25

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

theorem GlobalTheory.PMonE.WinCoef.frob_inv_pow_apply (n : ℕ) (x : F) :
    (((frobAut (F := F) p)⁻¹) ^ n) x = ((frobeniusEquiv F p).symm)^[n] x := by sorry
