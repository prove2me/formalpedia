-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_lowerOrder_normal
-- name    : GlobalTheory.PMonE.lowerOrder_normal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:39:29.279798+00:00
-- url     : https://prove2.me/theorems/a7418c3e-931d-4396-a67e-36fe614041ca
-- title:
--   PMon E: lower Order normal
-- statement:
--   The PMon E construction uses the lower Order normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSurjectivityOfOne.lean#L23-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSurjectivityOfOne.lean#L23-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
omit [Fintype m]

theorem GlobalTheory.PMonE.lowerOrder_normal {N : ℕ} (hN : 1 ≤ N) {M : ℕ → Matrix m m F} (hM : Normal (N + 1) M) :
    Normal N (lowerOrder N M) := by sorry
