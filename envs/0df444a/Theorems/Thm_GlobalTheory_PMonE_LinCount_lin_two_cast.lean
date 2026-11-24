-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_two_cast
-- name    : GlobalTheory.PMonE.LinCount.lin_two_cast
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:05.418479+00:00
-- url     : https://prove2.me/theorems/2eb9243a-7275-41bf-82c0-60a821c81c1d
-- title:
--   Lin Count: lin two cast
-- statement:
--   The Lin Count construction uses the lin two cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L59-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

theorem GlobalTheory.PMonE.LinCount.lin_two_cast (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M (k + 1 + 1)).mulVec Y (i.castSucc, a) = 0 := by sorry
