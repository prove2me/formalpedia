-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_root_eq
-- name    : GlobalTheory.KTypeCompare.root_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:09:57.519635+00:00
-- url     : https://prove2.me/theorems/2e410b9e-5cbf-58b7-9b8d-952452057ea0
-- title:
--   KType Compare: root eq
-- statement:
--   The KType Compare construction uses the root eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L15-L15

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

theorem GlobalTheory.KTypeCompare.root_eq (a b : Fin n) : PI.UpqRep.root a b = HarishChandraRootData.root a b := by sorry
