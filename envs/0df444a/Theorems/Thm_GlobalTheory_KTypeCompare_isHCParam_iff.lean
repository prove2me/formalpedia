-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_isHCParam_iff
-- name    : GlobalTheory.KTypeCompare.isHCParam_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:32.006209+00:00
-- url     : https://prove2.me/theorems/a77aed3e-5131-4ea6-b054-eef9d6c4c12d
-- title:
--   KType Compare: is HCParam iff
-- statement:
--   The KType Compare construction uses the is HCParam iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L38-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}

theorem GlobalTheory.KTypeCompare.isHCParam_iff (μ : Fin n → ℝ) : PI.UpqRep.IsHCParam μ ↔ HarishChandraRootData.IsHCParam μ := by sorry
