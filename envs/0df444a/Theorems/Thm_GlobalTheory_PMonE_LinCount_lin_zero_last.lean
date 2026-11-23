-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_zero_last
-- name    : GlobalTheory.PMonE.LinCount.lin_zero_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:43.882585+00:00
-- url     : https://prove2.me/theorems/24784c3c-2849-4a94-aea0-35129b999e62
-- title:
--   Lin Count: lin zero last
-- statement:
--   The Lin Count construction uses the lin zero last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L63-L65

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

theorem GlobalTheory.PMonE.LinCount.lin_zero_last (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M 0).mulVec Y (Fin.last K, a) = ∑ j : Fin (K + 1), (M j).mulVec (fun b => Y (j, b)) a := by sorry
