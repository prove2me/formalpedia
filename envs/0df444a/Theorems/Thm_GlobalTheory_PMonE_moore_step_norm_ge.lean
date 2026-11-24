-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_moore_step_norm_ge
-- name    : GlobalTheory.PMonE.moore_step_norm_ge
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:00.490536+00:00
-- url     : https://prove2.me/theorems/9ba0c107-08b7-4136-9d6c-23f77c596a69
-- title:
--   PMon E: moore step norm ge
-- statement:
--   The PMon E construction uses the moore step norm ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MoorePowSubSelfEqProd.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MoorePowSubSelfEqProd.lean#L51-L58

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

theorem GlobalTheory.PMonE.moore_step_norm_ge {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ c : ℤ, r ≤ ‖x + (c : F) * t‖) : r ^ p ≤ ‖x ^ p - t ^ (p - 1) * x‖ := by sorry
