-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_isClosed_stab
-- name    : GlobalTheory.Tw.PFlag.isClosed_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:56.797989+00:00
-- url     : https://prove2.me/theorems/206849e8-88e3-45ee-aca0-78a3b96521d3
-- title:
--   PFlag: is Closed stab
-- statement:
--   The PFlag construction uses the is Closed stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L252-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L252-L253

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

theorem GlobalTheory.Tw.PFlag.isClosed_stab : IsClosed (F.stab : Set (GL (Fin n) ℂ)) := by sorry
