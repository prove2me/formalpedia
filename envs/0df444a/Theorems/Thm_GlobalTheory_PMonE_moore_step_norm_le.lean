-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_moore_step_norm_le
-- name    : GlobalTheory.PMonE.moore_step_norm_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:33.101802+00:00
-- url     : https://prove2.me/theorems/78069acc-51ae-4701-af36-e6df2f1b9d1b
-- title:
--   PMon E: moore step norm le
-- statement:
--   The PMon E construction uses the moore step norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MoorePowSubSelfEqProd.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MoorePowSubSelfEqProd.lean#L60-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
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
open Finset Polynomial

theorem GlobalTheory.PMonE.moore_step_norm_le {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] (x t : F)
    (h : ‖t‖ ≤ ‖x‖) : ‖x ^ p - t ^ (p - 1) * x‖ ≤ ‖x‖ ^ p := by sorry
