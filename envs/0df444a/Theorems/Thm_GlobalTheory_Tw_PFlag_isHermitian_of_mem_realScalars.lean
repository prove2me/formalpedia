-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_isHermitian_of_mem_realScalars
-- name    : GlobalTheory.Tw.PFlag.isHermitian_of_mem_realScalars
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:28.944894+00:00
-- url     : https://prove2.me/theorems/2ff33ae8-d8dd-4b2a-aeca-fd5931094790
-- title:
--   PFlag: is Hermitian of mem real Scalars
-- statement:
--   The PFlag construction uses the is Hermitian of mem real Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L360-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L360-L376

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

theorem GlobalTheory.Tw.PFlag.isHermitian_of_mem_realScalars {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ F.realScalars) : X.IsHermitian := by sorry
