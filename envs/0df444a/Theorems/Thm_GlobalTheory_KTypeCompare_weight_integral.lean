-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_weight_integral
-- name    : GlobalTheory.KTypeCompare.weight_integral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:58:07.308252+00:00
-- url     : https://prove2.me/theorems/07421ed5-69b6-4f30-9f24-48f6c7659ee7
-- title:
--   KType Compare: weight integral
-- statement:
--   The KType Compare construction uses the weight integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L134-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L134-L171

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

theorem GlobalTheory.KTypeCompare.weight_integral {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H} {ω : Fin n → ℝ} {v : H}
    (h : HarishChandraRootData.IsWeightVector σ ω v) (a : Fin n) : ∃ m : ℤ, ω a = m := by sorry
