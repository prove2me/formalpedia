-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_isHCTypeU_iff
-- name    : GlobalTheory.KTypeCompare.isHCTypeU_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:20.405359+00:00
-- url     : https://prove2.me/theorems/f9ed8f8b-1051-44aa-bea3-f78eec159077
-- title:
--   KType Compare: is HCType U iff
-- statement:
--   The KType Compare construction uses the is HCType U iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L308-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L308-L333

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

theorem GlobalTheory.KTypeCompare.isHCTypeU_iff {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : Fin k → ℝ) (π : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H) :
    PI.UpqRep.IsHCTypeU k u π ↔ HarishChandraRootData.IsCompactIrrep π u := by sorry
