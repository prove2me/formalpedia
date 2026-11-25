-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_isURepOn_iff
-- name    : GlobalTheory.KTypeCompare.isURepOn_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:30.570561+00:00
-- url     : https://prove2.me/theorems/8145a8b5-491f-4235-83cf-2d671b3e43d5
-- title:
--   KType Compare: is URep On iff
-- statement:
--   The KType Compare construction uses the is URep On iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L89-L96

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem GlobalTheory.KTypeCompare.isURepOn_iff (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) :
    PI.UpqRep.IsURepOn G σ ↔ HarishChandraRootData.IsUnitaryRepOn G σ := by sorry
