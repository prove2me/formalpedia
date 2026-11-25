-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_lowK_allPos
-- name    : GlobalTheory.KTypeCompare.lowK_allPos
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:57:37.309911+00:00
-- url     : https://prove2.me/theorems/e12148c5-f11f-5892-9464-3249082b4fa7
-- title:
--   KType Compare: low K all Pos
-- statement:
--   The KType Compare construction uses the low K all Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L294-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L294-L306

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

theorem GlobalTheory.KTypeCompare.lowK_allPos (k : ℕ) (u : Fin k → ℝ) :
    PI.UpqRep.lowK (PI.UpqRep.allPos k) u = u - HarishChandraRootData.rhoU k := by sorry
