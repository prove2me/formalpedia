-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_isClosed_lieN
-- name    : GlobalTheory.Tw.PFlag.isClosed_lieN
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:33.054783+00:00
-- url     : https://prove2.me/theorems/c916f235-cb2a-4962-bdd7-140a09e52684
-- title:
--   PFlag: is Closed lie N
-- statement:
--   The PFlag construction uses the is Closed lie N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L250-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L250-L250

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

theorem GlobalTheory.Tw.PFlag.isClosed_lieN : IsClosed (F.lieN : Set (Matrix (Fin n) (Fin n) ℂ)) := by sorry
