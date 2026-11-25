-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_isWtOn_iff_of_torus
-- name    : GlobalTheory.KTypeCompare.isWtOn_iff_of_torus
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:32.603086+00:00
-- url     : https://prove2.me/theorems/46dc5200-941a-4a68-8f10-4d2b1e6aae81
-- title:
--   KType Compare: is Wt On iff of torus
-- statement:
--   The KType Compare construction uses the is Wt On iff of torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L98-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L98-L109

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

theorem GlobalTheory.KTypeCompare.isWtOn_iff_of_torus (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (hG : ∀ θ, HarishChandraRootData.torus θ ∈ G)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) (v : H) :
    PI.UpqRep.IsWtOn G σ ω v ↔ v ∈ HarishChandraRootData.weightSpace σ ω := by sorry
