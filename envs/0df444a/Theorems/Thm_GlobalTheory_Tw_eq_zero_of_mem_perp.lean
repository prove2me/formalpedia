-- Prove2me | Theorems.Thm_GlobalTheory_Tw_eq_zero_of_mem_perp
-- name    : GlobalTheory.Tw.eq_zero_of_mem_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:11.862734+00:00
-- url     : https://prove2.me/theorems/f0e17977-a3a5-4f2a-adf5-d7d38842c876
-- title:
--   Tw: eq zero of mem perp
-- statement:
--   The Tw construction uses the eq zero of mem perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L286-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L286-L287

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

theorem GlobalTheory.Tw.eq_zero_of_mem_perp {V : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℂ} (h : v ∈ V) (h' : v ∈ perp V) : v = 0 := by sorry
