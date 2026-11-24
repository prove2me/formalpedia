-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LinCount_lin_normal
-- name    : GlobalTheory.PMonE.LinCount.lin_normal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:38:46.864997+00:00
-- url     : https://prove2.me/theorems/4a1458a4-ddc1-4895-a8c5-8ad2aebb06be
-- title:
--   Lin Count: lin normal
-- statement:
--   The Lin Count construction uses the lin normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L20-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSolutionCountOfOrderOne.lean#L20-L41

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

theorem GlobalTheory.PMonE.LinCount.lin_normal (K : ℕ) (M : ℕ → Matrix m m F) (h : Normal (K + 1) M) : Normal 1 (lin K M) := by sorry
