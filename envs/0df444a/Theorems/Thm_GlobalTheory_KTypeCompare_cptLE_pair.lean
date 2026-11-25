-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_cptLE_pair
-- name    : GlobalTheory.KTypeCompare.cptLE_pair
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:24.750655+00:00
-- url     : https://prove2.me/theorems/7a711799-9655-400d-88b4-b1f6b0c53699
-- title:
--   KType Compare: cpt LE pair
-- statement:
--   The KType Compare construction uses the cpt LE pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L173-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L173-L191

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

theorem GlobalTheory.KTypeCompare.cptLE_pair {ε : Fin n → Bool} {ω Λ : Fin n → ℝ} (h : HarishChandraRootData.CptLE ε ω Λ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - ω) i ≤ 0 := by sorry
