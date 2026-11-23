-- Prove2me | Theorems.Thm_GlobalTheory_Tw_eq_zero_of_dot_star
-- name    : GlobalTheory.Tw.eq_zero_of_dot_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:52.864188+00:00
-- url     : https://prove2.me/theorems/65f27fb4-28f4-4ebc-b8fe-4c00241223ac
-- title:
--   Tw: eq zero of dot star
-- statement:
--   The Tw construction uses the eq zero of dot star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L284-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L284-L284

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
open scoped ComplexOrder

theorem GlobalTheory.Tw.eq_zero_of_dot_star {v : Fin n → ℂ} (h : v ⬝ᵥ star v = 0) : v = 0 := by sorry
