-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_summand_le_perp
-- name    : GlobalTheory.Tw.PFlag.summand_le_perp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:06.913992+00:00
-- url     : https://prove2.me/theorems/5a2f808f-6749-4ac7-85a1-e2a451a92e34
-- title:
--   PFlag: summand le perp
-- statement:
--   The PFlag construction uses the summand le perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L320-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L320-L321

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
open GlobalTheory.Tw.PFlag
variable {F : PFlag n ℂ}

theorem GlobalTheory.Tw.PFlag.summand_le_perp {V V' : Submodule ℂ (Fin n → ℂ)} (hV : V ∈ F.carrier) (h : V < V') : F.summand V' ≤ perp V := by sorry
