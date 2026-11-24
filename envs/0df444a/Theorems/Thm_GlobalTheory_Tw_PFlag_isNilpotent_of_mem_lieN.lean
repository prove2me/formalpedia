-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_isNilpotent_of_mem_lieN
-- name    : GlobalTheory.Tw.PFlag.isNilpotent_of_mem_lieN
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:13:30.756916+00:00
-- url     : https://prove2.me/theorems/c8de8ead-06a4-4c76-962a-8608357069ce
-- title:
--   PFlag: is Nilpotent of mem lie N
-- statement:
--   The PFlag construction uses the is Nilpotent of mem lie N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L185-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L185-L197

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
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}

theorem GlobalTheory.Tw.PFlag.isNilpotent_of_mem_lieN {X : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieN) : IsNilpotent X := by sorry
