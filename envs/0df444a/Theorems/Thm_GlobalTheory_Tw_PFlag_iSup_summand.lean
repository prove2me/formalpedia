-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_iSup_summand
-- name    : GlobalTheory.Tw.PFlag.iSup_summand
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:13.219183+00:00
-- url     : https://prove2.me/theorems/8ab7b7c9-c3bb-5b1b-8994-8e95cffae412
-- title:
--   PFlag: i Sup summand
-- statement:
--   The PFlag construction uses the i Sup summand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L317-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L317-L318

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

theorem GlobalTheory.Tw.PFlag.iSup_summand (F : PFlag n ℂ) : ⨆ V ∈ F.carrier, F.summand V = ⊤ := by sorry
