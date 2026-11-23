-- Prove2me | Theorems.Thm_GlobalTheory_Tw_dot_star_comm_zero
-- name    : GlobalTheory.Tw.dot_star_comm_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:38.729666+00:00
-- url     : https://prove2.me/theorems/9f466885-fb36-4796-bc73-0b47ea3fa6f4
-- title:
--   Tw: dot star comm zero
-- statement:
--   The Tw construction uses the dot star comm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L277-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L277-L279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ}

theorem GlobalTheory.Tw.dot_star_comm_zero {v w : Fin n → ℂ} (h : v ⬝ᵥ star w = 0) : w ⬝ᵥ star v = 0 := by sorry
