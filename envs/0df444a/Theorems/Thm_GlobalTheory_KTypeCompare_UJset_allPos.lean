-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_UJset_allPos
-- name    : GlobalTheory.KTypeCompare.UJset_allPos
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:10.122871+00:00
-- url     : https://prove2.me/theorems/b396230f-b58b-4001-9e4b-d4c2d1ea9625
-- title:
--   KType Compare: UJset all Pos
-- statement:
--   The KType Compare construction uses the UJset all Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L286-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L286-L292

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

theorem GlobalTheory.KTypeCompare.UJset_allPos (k : ℕ) : PI.UpqRep.UJset (PI.UpqRep.allPos k) =
    (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by sorry
