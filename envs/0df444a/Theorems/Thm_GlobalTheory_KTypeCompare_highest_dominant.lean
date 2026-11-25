-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_highest_dominant
-- name    : GlobalTheory.KTypeCompare.highest_dominant
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:23.395048+00:00
-- url     : https://prove2.me/theorems/b3b261af-718f-44ab-9e73-37955658521b
-- title:
--   KType Compare: highest dominant
-- statement:
--   The KType Compare construction uses the highest dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L193-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L193-L282

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

theorem GlobalTheory.KTypeCompare.highest_dominant {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H}
    (hσ : HarishChandraRootData.IsUnitaryRepOn (HarishChandraRootData.grpK ε) σ) {S : Submodule ℂ H} {Λ : Fin n → ℝ}
    (h : HarishChandraRootData.IsKType ε σ S Λ) {a b : Fin n} (hab : a < b) (hε : ε a = ε b) : Λ b ≤ Λ a := by sorry
