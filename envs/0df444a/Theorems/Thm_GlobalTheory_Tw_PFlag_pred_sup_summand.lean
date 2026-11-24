-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_pred_sup_summand
-- name    : GlobalTheory.Tw.PFlag.pred_sup_summand
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:15.441711+00:00
-- url     : https://prove2.me/theorems/cb108e5f-483c-4e42-8f4e-71103f958ed6
-- title:
--   PFlag: pred sup summand
-- statement:
--   The PFlag construction uses the pred sup summand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L307-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L307-L308

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

theorem GlobalTheory.Tw.PFlag.pred_sup_summand (F : PFlag n ℂ) (V : Submodule ℂ (Fin n → ℂ)) : F.pred V ⊔ F.summand V = V := by sorry
