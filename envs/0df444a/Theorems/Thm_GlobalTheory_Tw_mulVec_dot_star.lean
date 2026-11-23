-- Prove2me | Theorems.Thm_GlobalTheory_Tw_mulVec_dot_star
-- name    : GlobalTheory.Tw.mulVec_dot_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:56.739256+00:00
-- url     : https://prove2.me/theorems/15294c79-51db-4bc7-96cb-ea2e1c80c382
-- title:
--   Tw: mul Vec dot star
-- statement:
--   The Tw construction uses the mul Vec dot star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L273-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L273-L275

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

theorem GlobalTheory.Tw.mulVec_dot_star (X : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    (X *ᵥ v) ⬝ᵥ star w = v ⬝ᵥ star (Xᴴ *ᵥ w) := by sorry
