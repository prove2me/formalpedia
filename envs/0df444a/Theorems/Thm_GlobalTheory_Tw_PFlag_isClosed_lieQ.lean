-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_isClosed_lieQ
-- name    : GlobalTheory.Tw.PFlag.isClosed_lieQ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:44.202857+00:00
-- url     : https://prove2.me/theorems/a3767a5e-8ed8-460e-8c85-00ddbcfd3ab1
-- title:
--   PFlag: is Closed lie Q
-- statement:
--   The PFlag construction uses the is Closed lie Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L248-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L248-L248

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
open GlobalTheory.Tw.PFlag
variable {n : ℕ} (F : PFlag n ℂ)

theorem GlobalTheory.Tw.PFlag.isClosed_lieQ : IsClosed (F.lieQ : Set (Matrix (Fin n) (Fin n) ℂ)) := by sorry
